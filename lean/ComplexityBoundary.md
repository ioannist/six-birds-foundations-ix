# The complexity boundary for audited Markov reachability

A lawful rational state $B$ is finely reachable from a lawful rational state $A$ when every positive rational tolerance admits a finite edit chain of lawful rational states from $A$ to $B$. Each state carries a law and a profile. At a fixed profile, a step requires the sup distance between the prepared marked transition tables to be strictly below the tolerance. The held tests are exact at every point of the chain.

**Theorem (complexity of audited Markov reachability).** Take the full instrument class of Theorem 2.1, with explicitly presented finite instrument data and supplied lawful rational states $A,B$. A route licence compares equal-duration events as specified below.

1. **Single-word tests.** If each side of every licence contains one word, fine reachability on these promised-lawful inputs is P-complete under deterministic log-space many-one reductions. The polynomial-time decision is
   $$
   A\leadsto_{\mathrm{fine}}B
   \quad\Longleftrightarrow\quad
   p_A\preceq p_B
   \ \text{and}\
   \operatorname{SCore}_{p_A}(\alpha_A)=\operatorname{SCore}_{p_A}(\alpha_B),
   $$
   using the source profile's spectral rows, including the reversal equations. Both verdicts have polynomial-size, polynomial-time checkable certificates. Hardness already holds at a common fixed profile with a binary base, one parity probe, one register value, grade zero, full support, identity reversal, all words of length three, response cap $1/2$, one calibration to $1/4$, and uniformly equal mark rates fixed by the floor. The endpoints differ only in the sign of one response. [Log-space reduction and Lean correspondence](SingleWordHardness.md)
2. **Exactly one two-word licence.** If exactly one licence compares a single word with two distinct words and every other licence compares single words, fine reachability is PSPACE-hard under polynomial-time many-one reductions. This holds with all licences held at a common fixed profile, a singleton register, identity mark reversal, response cap $1/2$, a positive rate floor, and two distinct lawful rational endpoints. The unique widened licence can have duration one or duration two, and every other licence has duration three. The same reduction proves PSPACE-hardness of chain existence at a supplied positive inverse-polynomial tolerance.

The [algebraic boundary and fixed-count quartic corollary](BoundaryCorollaries.md)
give the corresponding model-free statement and the conditional
fixed-parameter undecidability result.

## Input conventions and measured tests

For the signed binomial problem, inputs list the coordinates, rows, guards and two rational endpoints explicitly. Exponents and rational numerators and denominators are encoded in binary. Boundedness of the rational lawful locus is a promise, as in Theorem 3.5. For Theorem 2.1 the native instrument is the parity/refresh instrument of [§2](../paper/sections/model.tex), including its held license and publication catalogues, rate floor, register weights and reversal. Input sets, partitions, probes, words and laws are given by explicit lists or tables. The endpoints are promised lawful, including the policy test. The decision algorithm need not evaluate the policy or enumerate attained profiles. Prepared transition tables may replace the numerical law data. The endpoint profiles or their named readouts must still be given, since a prepared table can occur with different held catalogues. The test rows may be supplied precompiled.

For the widened class, keep the native law, rate floor, guards, register, profiles, publication catalogue and licence policy of Theorem 2.1. Extend the route licence syntax by the joint masses of the [finite-event extension in Appendix B](../paper/sections/companion.tex). For a preparation $(g,u)$ and projected endpoint $h$, write $J_A(w;(g,u),h)$ for the measured joint probability of the word $w$ and that endpoint. The joint mass of the event and endpoint $h$ is the sum of $J_A$ over the distinct words in the event. The event mass from $(g,u)$ is the sum of these joint masses over $h$. The two sides of a licence must give the same joint masses for every preparation and projected endpoint. They are nonempty, have the same positive duration within the instrument horizon, and use either one word on each side or one word against two. The direction of the comparison is immaterial because it is an equality.

For singleton sides, summing over projected endpoints recovers equality of the two positive word masses, and dividing by that mass recovers equality of their conditional projected endpoint laws. Conversely, these two equalities give equality of the joint masses. Thus the singleton sublanguage is precisely the route test of Theorem 2.1. The attained profiles are those with a lawful rational state under the catalogue in use. Use the same directed profile order and the same edits of §2 of the manuscript, with covers in this attained order. A cover preserves the prepared law if the proposal support agrees and the projected marked law if the support shrinks. In the native coordinates these are, respectively, equality of physical laws and equality of rates and spectral responses. The native readout and the transition formula identify the corresponding data in both directions. The numerical tolerance remains on the prepared marked table.

In the one-state subclass the base and register are singletons, the probe family is empty, and marks are self-reversing. Each prepared marked table has a single entry, the mark rate. The conditional projected endpoint is the same point mass for each nonempty event, so every licence is exactly the comparison of the sums of its word-rate products. This applies to the one-state construction in §2.2 and the supporting proposition in §3.

## 1. Proof of the polynomial-time arm

For the singleton-word part of the theorem, the measured interpretation above gives exactly the hypotheses of Theorem 2.1. Its signed-core criterion reduces the task to checking $p_A\preceq p_B$ and computing two signed cores for the source tests. The bounded signed binomial class of Theorem 3.5 uses the same core computation. For a support $S$, form $A_S$ from the integer exponent differences of the active rows. Given $S$, solve the rational linear program

$$
\max \sum_{j\in S}z_j,\qquad A_Sw=0,\quad w\ge0,\quad 0\le z_j\le 1,\quad z_j\le w_j.
$$

A coordinate is removable precisely if some feasible $w$ has its coordinate positive. Sum one such $w$ for each removable coordinate and scale the result by a positive rational so all removable coordinates are at least one. This attains the maximum possible objective, namely the number of removable coordinates. In every optimum the $z_j$ therefore equal one on all removable coordinates and zero elsewhere, and the same $w$ vanishes precisely on the surviving coordinates. Clearing the denominators gives integral weights for the resulting contraction. Recompute the active rows. Every nonterminal round loses at least one coordinate. Counting the terminal optimization on a nonempty support, there are at most $n$ support rounds. The least-support and restriction lemmas of Theorem 3.5 identify the final support with the core. Comparing the two core supports and signs decides fine reachability.

Each LP has at most $d=2n$ variables, one equation per active row, and at most $4n$ other inequalities. Its matrix entries are bounded in magnitude by $D_0=\max\bigl(\{1\}\cup\{|u_i-v_i|:\ (u,v)\text{ is a row and }i\text{ is a coordinate}\}\bigr)$, and its right sides are zero or one. The polyhedron is nonempty and pointed because all its variables are nonnegative. The objective is bounded and the optimal face has a vertex. At that vertex take $d'$ independent incident rows in the $d'=2|S|$ variables. By Cramer's rule a single positive integer denominator clears all the coordinates, and both it and the magnitudes of the resulting numerators are at most $(2n)!D_0^{2n}$. In particular the integral damping weights have at most $1+\lceil\log_2((2n)!D_0^{2n}+1)\rceil$ bits each. Rational linear programming finds the optimal value and an optimal vertex in time polynomial in the binary size. One can also find a vertex by successively minimizing each coordinate on the previous minimizing face of the optimum, with at most $2n$ additional calls per round. Each such face is a face of the original polyhedron, so the original determinant bound controls the bit sizes of the appended equalities. The support/sign computation and comparison use only the resulting integer weights and endpoint signs.

To validate a binomial test $x^u=cx^v$, detect a vanishing monomial by looking for a zero coordinate with a positive exponent, using $0^0=1$. If $c=0$, accept exactly when $x^u$ vanishes. For $c\ne0$, if either monomial vanishes, accept exactly when both vanish. In the remaining case, compare the signs, including the sign of $c$, by exponent parity. Then compare the two positive rational power products. A gcd-free refinement writes the listed integer numerator and denominator bases as products of powers of a pairwise coprime integer basis. Track denominators as negative exponents and include the coefficient's numerator and denominator with powers $1$ and $-1$ respectively on the right. Equality of the resulting exponent vectors is equivalent to equality of the positive rational products. Factor refinement and the integer exponent arithmetic are polynomial in the binary input. Guards use rational arithmetic.

For the native input let $n=|M||I|$ be the number of spectral coordinates. At the source profile there are $n+|I||\Lambda|+a$ spectral rows, where $\Lambda$ is the set of held licenses and $a$ is the number of held calibration publications. These are respectively reversal equalities, one word-count row per held license and probe, and one unit row per calibration. A ratio publication adds no spectral row. All word counts and exponent differences are bounded by the maximum of one and the largest explicit word length. Read each rate from a prepared row sum and each response by the signed query divided by its positive rate. If a prepared table has $N=|X||R|$ columns, each such numerator or denominator is a sum of at most $N$ binary rationals. A product of their denominators clears the sum and has bit length at most their total bit length. Division introduces at most the sum of the operand bit lengths, up to a constant. A register partition is compared by testing that two elements in the same target block are in the same source block at each grade, with at most $(g+1)|R|^2$ comparisons for grades $0$ through $g$. The support can be read by at most $|M||X|^2|R|^2$ zero tests per endpoint, and the catalogues are compared by inclusion. Thus these operations, including writing the dense exponent vectors, have polynomial time and output size in the explicit data. Reject when the directed profile comparison fails. Otherwise the target satisfies the source tests by inheritance, and Theorem 2.1 identifies native fine reachability with equality of the signed cores for those tests. When validating the standalone spectral inputs beyond the lawful-input promise, the gcd-free test above avoids expanding binary exponents.

### Certificates

For each endpoint record the successive integral weight vectors and one final vector of integral multipliers on the active rows at the terminal support $C$. The checker computes supports by retaining exactly the zero-weight coordinates, and checks each balance against the rows active **at that round**. At the terminal support check $A_C^{\mathsf T}\lambda>0$ coordinatewise. This forces $w=0$ in the nonnegative kernel, by taking the dot product. The final support is therefore irreducible. The least-support theorem implies that an attained irreducible support is the core. Empty support has a vacuous dual check.

For completeness of the certificate, a real nonzero nonnegative vector in the kernel would give a rational one, by rational linear feasibility with some coordinate at least one. Thus at an irreducible support there is no such real vector. The theorem of alternatives supplies the strict positive row combination. Equivalently, zero is outside the convex hull of the columns of $A_C$, and a functional strictly separates this compact convex hull from zero. Scale the dot products to be at least one and choose rational multipliers of polynomial bit length, by linear programming or the determinant argument in §4. The terminal determinant bound in §4 gives at most $n$ nonzero integral multipliers of magnitude at most $n!D_0^n$. With $m$ listed test rows, one certificate can be stored with $O(n^3(1+\log(n+1)+\log D_0)+n\log(m+1))$ bits using sparse terminal multipliers and at most $n$ stages. The dense checker can instead fill the omitted $m$ entries with zeros. Every weight test compares sums of $n$ products of numbers of polynomial bit length, and the terminal check evaluates at most $nm$ such products. The signed comparison is polynomial in the endpoint and certificate sizes. This gives polynomial-size certificates for both verdicts. The signs are checked on the original rational endpoint values in the computed supports. For different native profiles the verifier also checks the directed order. A failed order comparison itself certifies a negative answer.

A positive certificate gives a compact edit prescription. On its first half, perform the stated monomial contractions. Interpolate within the common signed chart using the guard-preserving rational realization lemmas, then reverse the contractions at the other endpoint. The existing rational realization lemmas give finite lawful rational chains at every prescribed mesh. This is a certificate for existence at every mesh. Literal expansion into a list of rational points need not be polynomial-size. On the rational curve $x_{i+1}=x_i^2$ in $[0,1]^{n+1}$, every chain with tolerance $1/4$ from the all-zero to the all-one point visits a point with $x_0\in[1/4,1/2)$. Its reduced denominator is at least two. The reduced denominator of $x_n=x_0^{2^n}$ has at least $2^n+1$ bits. In the directed native theorem the support covers, affine register interpolation, homogeneous rate path, and final capability covers are realized as in the existing transfer. The verifier need not produce a smallest cover chain.

## 2. Hardness in the measured instrument

### 2.1. Proof with exactly one two-word licence

Use configuration-to-configuration Nondeterministic Constraint Logic (NCL).
Its instances have two specified legal orientations of an AND/OR constraint graph,
and a move reverses one edge while preserving all minimum inflows. The problem
is PSPACE-complete by Hearn and Demaine, Corollary 6. The proof there supplies
distinct legal orientations. [Hearn and Demaine, §2 and Corollary 6](https://arxiv.org/abs/cs/0205005)

A licence compares the full joint endpoint table. Write $\mu(w)$ for the
product of mark rates in a word and $b_j(w)$ for the product of its responses
at probe $j$. Because the register rows sum to one, the projected joint
endpoint table is a linear combination of the uniform projector and the
pairwise orthogonal probe projectors. Its coefficients are $\mu(w)$ and
$\mu(w)b_j(w)$. Thus $u\sim\{v,w\}$ holds exactly when the mass
equation and every probe equation hold.

$$
 \mu(u)=\mu(v)+\mu(w),\qquad
 \mu(u)b_j(u)=\mu(v)b_j(v)+\mu(w)b_j(w)\quad(j\in I).
$$

The compared word lists yield one mass equation and one equation per probe
from this single licence. These equations may be redundant for particular
words or calibrations. Their derivation uses the same character-product
calculus as the singleton compilation in Theorem 2.1.

The [full proof and bit bounds](SingleAdditiveLicence.md) give a binary base
of size linear in the number of edges, one probe per edge and a reserve probe.
The sole widened comparison, $LL\sim\{AL,BL\}$, forces a fixed rate vector
via the floor and gives $x_j+y_j=k$ at each probe. Single-word comparisons
force the full outgoing charge whenever the associated toggle is nonzero.
Each vertex's response budget enforces the NCL capacity. A legal flip lifts
through preloading the new charge, interpolating the toggles, and unloading
the old charge. For floor $r$ and toggle sum $k$, a step at the supplied
tolerance $rk/(2|X|+1)$ shares a represented orientation between its
endpoints. Thus a chain at the supplied tolerance exists exactly when the
source orientations are flip-connected. Fine reachability has the same
criterion. The argument allows a growing number of probes and one widened
catalogue entry. The common final mark can be cancelled in both the
mass and probe equations, so the same proof uses $L\sim\{A,B\}$ at
duration one. [Shortening argument](BoundedProbes.md#1-duration-one-in-the-hardness-construction).

Replacing the duration-two widened comparison by $LL\sim LL$ at the
same name preserves both supplied endpoints and makes every instance
from this construction a yes-instance. [One-licence verdict control](SingleAdditiveLicence.md#7-the-one-licence-verdict-control).

### 2.2. Supporting one-state hardness result

**Proposition.** Fine reachability is PSPACE-hard in the probe-free one-state
subclass with duration-two licences, a fixed profile, a positive rate floor
and two distinct supplied lawful rational endpoints, allowing a growing
number of singleton-versus-pair licences. The same reduction proves hardness
at a supplied positive inverse-polynomial tolerance.

Instantiate the widened class on one state. Give each compiled test its own named licence, including tests with singleton sides. Use the policy that holds exactly the full catalogue, one disclosure grade and no publications. The register weight is one and the response cap is zero. The unique register law and the singleton partitions fix the support and the disclosure profile. Thus all lawful states have the same profile. The class's edit relation on this subclass consists of the same rate-metric rewrites used below, since a strict profile cover between such states is impossible. The common horizon is two.

#### A cubical realization that preserves reachability

Use the PSPACE-complete two-solution connectivity problem for 3-CNF. [Gopalan, Kolaitis, Maneva and Papadimitriou, Lemma 3.6](https://arxiv.org/pdf/cs/0609072#page=13). The two given assignments already satisfy the formula. To restrict to distinct endpoints, map instances with equal endpoints to a fixed yes instance with two distinct adjacent satisfying assignments. Delete tautological clauses and retain nonempty clauses (an empty unsatisfied clause is excluded on these instances). Duplicate literals within a clause are harmless. For a coordinate $x_i\in[0,1]$, declare a positive literal true at $x_i=1$ and a negative literal true at $x_i=0$. Require one literal true in each clause, with these endpoint meanings. Call the resulting rational cube locus $D$.

For $x\in D$, the smallest closed cube face containing $x$ fixes the coordinates of $x$ which are already zero or one. Every vertex of that face satisfies the formula, because each clause has a literal true at one such fixed coordinate. Conversely, if a face has all its vertices satisfying, then every clause has a true fixed literal. Otherwise, assign its remaining literals to be false, which is possible because the clause is non-tautological, and complete to a vertex. This would contradict satisfaction. These faces are the induced cubical complex of the satisfying assignments. Its vertices are the satisfying assignments and its edges are the satisfying single-bit flips. [Schnider and Weber, Definition 1.5](https://arxiv.org/abs/2307.03446).

Here is the exact rational-chain argument. An allowed flip gives an entire lawful rational segment, so a flip sequence gives chains of every mesh. Conversely, two points of $D$ at sup distance strictly less than one cannot fix any coordinate to opposite endpoints. Their smallest cube faces have a common vertex. Within either face all corner vertices are joined by single-bit flips. Apply this at each link of a chain, starting and ending at the specified vertices. A mesh-one chain yields a Boolean flip chain. Each point of $D$ determines a Boolean flip class via any vertex of its smallest cube face. The common-vertex argument shows that points in different flip classes have sup distance at least one. This does not depend on existence of a continuous path of rational points.

#### Compilation into the native instrument

Let the cube have coordinates $x_i\in\mathbb Q\cap[0,1]$, and let each equation be between positive expressions built from $1$, $A_i=1+2x_i$, $B_i=3-2x_i$, addition and multiplication. Define the bound of an expression by replacing both kinds of leaves $A_i,B_i$ by $3$ and evaluating using integer arithmetic. All subexpressions have values between one and their bounds throughout the cube. Enumerate the $q$ distinct expression nodes. If $B$ is the largest node bound (zero when the list is empty), take $k=\max(2,\lceil\log_2(B+1)\rceil)$ and $C=2^k$.

Use two distinct reference marks at each level $j=0,\ldots,k$, each of rate $2^jr$. Compare the copies and enforce doubling by summing the two distinct copies of the previous level. For each coordinate use a pair of rates $rA_i,rB_i$ with pair sum $4r$. For each node provide two copies of an output/complement pair of sum $Cr$. Compare the output copies. Use one equation to compute each node output, and one output comparison per original equation. A constant outputs $r$, a coordinate leaf outputs its coordinate rate, an addition outputs $a+b$, and a product outputs $ab/r$. For an addition use the first copy of its left child and the second copy of its right child. The marks are distinct even when the children are equal. Use a common pad of rate $r$ for every singleton equality and every sum, and realize $z=ab/r$ by comparing the word $(z,\mathrm{root})$ with $(a,b)$. Every test lists one word against at most two distinct words, all of duration exactly two.

With $n$ coordinates and $m$ input equations the catalogue has
$$
  N=2(k+1)+2n+4q\quad\text{marks},\qquad
  T=2k+1+n+4q+m\quad\text{tests}.
$$
The total of the rate multiples is $K=2(2^{k+1}-1)+4n+2q C$. Supply the rate floor $r=1/K$. Write $r'$ for the actual first reference rate in a lawful point. Each reference-copy, doubling and pair-sum equality can be divided by the padded positive root rate. They force the reference rates and all pair totals to be the claimed multiples of $r'$. Normalization then forces $r'=r$. The coordinate pairs and their floors give $0\le x_i=(a_i/r-1)/2\le1$. By induction over expression nodes, their output rates are exactly $r$ times their expression values. Each complement is fixed by its pair total. Conversely these assignments satisfy every rate floor because the output value is between one and $C-1$. Their rates sum to one and the original equations are exactly the remaining tests. This proves a bijection on rational lawful points, including the supplied endpoints.

The prepared transition matrix for each mark has a single entry, its rate. A step of size strictly less than $2r\tau$ therefore projects to a cube step of size strictly less than $\tau$. In the other direction the rate lift is Lipschitz on the cube. For example, the expression variation bounds of the leaves $1,A_i,B_i$ are $0,2,2$. For an addition, sum the two variation bounds. For a product of nodes with bounds $B_a,B_b$ and variation bounds $L_a,L_b$, use $B_a L_b+B_b L_a$. Complements have the same variation as outputs. This means a sufficiently fine rational chain on the cube lifts to a lawful native chain at any prescribed positive tolerance. There can be no strict profile cover between the fixed-profile endpoints. This is the metric of the original edit relation.

For a Boolean clause write the product of the selected factors $B_i-1$ for positive literals and $A_i-1$ for negative literals. With pairs of positive expressions $(P,Q)$ for differences, use $(2,1)$ for the empty product and
$$
  (P-Q)(U-V)=(PU+QV)-(PV+QU).
$$
Thus the compiler imposes exactly the clause equation. For a clause of width $j\le3$, start with maximum node bound $2$ and total pair tree size $4$. Adding a literal multiplies the maximum bound by at most four, and changes the total tree size $s$ to $2s+10$. Hence $B\le128$, $k\le8$, and $q\le102m$. The tests have $O(1+n+m)$ entries with at most six mark IDs per test. The normalizer is $O(1+n+m)$ with a constant independent of the formula. The supplied endpoint coordinates are cube vertices, so each endpoint rate is an integer multiple of $1/K$ with numerator at most $K$. The singleton base and register, identity reversal and full support are specified with at most $O(N\log(2+N))$ bits even if explicitly tabulated. Name the licences by their indices in the catalogue. Present the policy as a list of allowed held subsets with a single entry, the full catalogue. The names and this policy have at most $O(T\log(2+T))$ additional bits. The full binary output length is $O((1+n+m)\log(2+n+m))$. Expression numbering can be done by comparing the bounded-size subtrees with binary coordinate identifiers. All emitted arrays, tests, floor and endpoints can be written in polynomial time. Combined with the cube result, this proves the PSPACE lower bounds for fine reachability and for the supplied inverse-polynomial tolerance $2/K$. The same equivalence holds at each positive tolerance at most $2/K$, in particular at the rate floor $1/K$.

#### Tractable event restrictions in the one-state subclass

At a fixed, publication-free one-state profile, duration-one event equalities are linear in the rate vector. The simplex and rate floor are also linear, so the rational segment between lawful endpoints gives a lawful rational mesh at every tolerance. For singleton words of any equal duration, the rate equations have equal degrees on the two sides. The native rate-fiber theorem gives fine connectivity. Its Lean proof applies signed-chart connectivity to the raw rates $v_m$ and inverse coordinates $b_m$, with $v_mb_m=1$, $|b_m|\le 1/\delta$ and the additional guard $\sum_m |v_m|\le1$. The inverse guards enforce $|v_m|\ge\delta$ before normalization. Dividing by the positive sum of raw magnitudes, which is at most one, preserves that floor. Equal word degrees preserve the tests under normalization. To transfer a mesh, write $S=\sum_m |v_m|$ and $S'=\sum_m |v_m'|$ for two raw points at sup distance below $\eta$. Both sums are at least $\delta$ and $|S-S'|<|M|\eta$. For each mark,
$$
\left|\frac{|v_m|}{S}-\frac{|v'_m|}{S'}\right|
\le \frac{\big||v_m|-|v'_m|\big|+|S-S'|}{S},
$$
since $|v'_m|/S'\le1$. A raw mesh of $\delta\varepsilon/(|M|+2)$ is therefore sufficient for tolerance $\varepsilon$. This is the transfer used in Lean, including positive fixed ratios on the singleton side.

## 3. Supporting proposition on rational roots

**Proposition.** The existence of a rational zero of an integer polynomial
reduces in polynomial time to fine reachability in a fixed-profile one-state
instrument with duration-two singleton-versus-singleton and
singleton-versus-pair licences, allowing a growing number of the latter. The
same reduction works at the supplied tolerance $2/K$ and at every positive
tolerance at most $2/K$. In the finite-event extension with arbitrary event
size and duration, the catalogue can also be compiled in polynomial time
into one joint-mass equality.

Take an integer polynomial in a sparse encoding with binary coefficients and exponents, of length $L$. The gate normalization uses the standard substitutions behind Shor normal form, which reduces real-root existence to linear trinomials and degree-at-most-two binomials. Below, the equations are solved over the rationals and circuit evaluation supplies the exact equivalence over that field. [Bihan, Rojas and Stella, §3.3, proof of Theorem 1(3)](https://arxiv.org/abs/math/0411107). Form an arithmetic circuit with $O(L+1)$ input and gate variables. Build each coefficient by its bits using addition and doubling from zero and one, with a negation for negative sign. Raise input variables to binary exponents by repeated squaring and multiply the selected powers and coefficients. Sum the terms and add one equation forcing the output to be zero. Discard unused variable names and relabel the remaining indices. Each exponent or coefficient bit requires at most a constant number of gates, and the number of term and factor delimiters is at most $L$. Consequently the gate list with binary pointers has $O((L+1)\log(2+L))$ bits. Input assignments extend uniquely to values of all the computation gates. The final zero equation is the polynomial's zero test. This includes constant and zero polynomials.

Use a box variable $p_z\in[-1,1]$ for each gate or input $z$, a common denominator $d\in[0,2]$, a selector $s\in[0,2]$, $w\in[1,3]$ and $u\in[-1,1]$. Homogenize the *local* gate equations using
$$
 p_z=0,\qquad p_z=d,\qquad p_z=p_a+p_b,\qquad p_z=-p_a,\qquad dp_z=p_ap_b.
$$
They are equivalent at $d>0$ to the rational gate equations on $p_z/d$. Add $w^2=2+d^2u$, and multiply the residual of each equation, including this last one, by $s(2-s)$. Take one cube vertex on each end face with the other cube coordinates zero. Both are automatically lawful. A lawful rational point at $0<s<2$ has $d>0$ because $w^2=2$ has no rational solution. Reading the quotients gives a rational circuit solution.

Conversely, let $v_z$ be a rational solution of the circuit equations and set $d=(1+\sum_z |v_z|)^{-1}$. Then $p_z=dv_z$ lies in $[-1,1]$. Choose a rational $w$ strictly between $\sqrt2$ and $\sqrt2+d^2/4$. Since $d\le1$ and $\sqrt2<3/2$, this gives $1<w<2$ and $0<w^2-2<d^2$. Set $u=(w^2-2)/d^2$. These coordinates give a lawful rational segment from $s=0$ to $s=2$. Each end face is a full box, giving a second and third rational segment that connect to the supplied endpoints. Affine interpolation at rational subdivisions gives lawful meshes at every positive rational tolerance. If there is no rational solution, all lawful rational points are on one of the two end faces, and any chain between the given endpoints must cross them in a single step. In the normalized cube coordinate $s/2$ that step has size one. Allowing real laws erases the obstruction. At $d=0$, all $p_z=0$, $u=0$, $w=\sqrt2$ satisfy the gated equations for every selector value, regardless of whether the circuit has a rational solution. Moreover every real interior point can move to an end face just by varying the selector. The real cube locus is therefore path-connected for every input. The rate compiler has the same algebraic proof over the reals and is continuous, so this also gives path connectivity of the real native law fiber.

For compilation, each of $s,d$ is $A_i-1=2x_i$, each of $u,p_z$ is $A_i-2$, and $w=A_i$. Express any residual as a difference of two positive trees. Use $(1,1)$ for zero, $(2,1)$ for one, $(A_i,1)$ for $2x_i$, coordinatewise pair addition, pair swap for negation, and the product rule in §2.2. These are a fixed finite collection of templates independent of circuit size. Quantitatively, for pair bounds $a,b$, addition or subtraction gives at most $a+b$ and multiplication at most $2ab$. Pairs for $p_z,u,w$ have bound at most five, those for $s,d$ at most three, and the pair for two at most four. The selector factor has bound at most $42$, the slack residual at most $234$, each other residual at most $234$, and each gated output at most $2\cdot42\cdot234=19656$. No tree has depth greater than eight (leaves have depth zero, a pair product raises maximum depth by two). Thus there are at most $1022$ nodes per equation, $k\le15$ and $K=O(L+1)$. The input/output counts and bit bound in §2.2 apply verbatim, so this is a polynomial-time many-one reduction in the binary polynomial input. Both tolerance $2/K$ and the coordinates of the two encoded endpoints have $O(\log(2+L))$ bits each. The possibly large witness $v$ is used only in the proof of correctness. The output construction never computes it.

### One held equality

Apply the manuscript's balanced-suffix construction for finite-event expressivity to the sum of squares of the short-test differences. Use the same occurrence-based encoding as in Lean. For each short test let $f_t$ be the left mass minus the right mass, a signed sum of two or three degree-two word products. Expand $F=\sum_t f_t^2$ as signed occurrences without collecting equal monomials. Each occurrence has a four-letter prefix obtained by concatenating the two words in that product. There are $\ell\le9T$ occurrences. Let $b=\lceil\log_2(\max(2,\ell))\rceil$. Number the occurrences from zero and use their $b$ binary digits to choose the ordering of the two root copies in each of $b$ consecutive suffix pairs. The suffixes all have mass $(\theta_i\theta_j)^b$ and distinguish even occurrences with identical prefixes. Assign the resulting words to the events according to their signs. A nonempty test catalogue contributes both signs since each test has a positive and a negative term, and its square contains a same-sign product and an opposite-sign product. The compiler always supplies a nonempty catalogue. Hence both events have positive mass on the positive rate simplex.

The resulting probability difference is $(\theta_i\theta_j)^b F$. With a positive floor this vanishes exactly when every short test holds. Replace the licence catalogue by the single compressed comparison and set the horizon to $4+2b$. The policy now allows exactly the held set containing that licence. Give both endpoints this new held set, keeping their rates, marks, floor, support and disclosure data.

In either instrument the policy fixes the held set and the one-state carrier fixes the other profile data. A lawful rate vector therefore determines a unique state for that instrument. The equality of the two rate loci gives a bijection of lawful states by keeping the rate vector and using the corresponding profile. Each step on either side is a fixed-profile rewrite and has the same distance under this bijection. Applying the map or its inverse at every point gives a bijection of chains at each tolerance, including chains between the two supplied endpoints. There are at most $9T$ words of length at most $4+2\lceil\log_2(\max(2,9T))\rceil$, and the explicit output uses $O(T\log(2+T)\log(2+N))$ bits.

## 4. Effective separation

Let $L$ be the binary length of the coordinate list, tests and guards, excluding the endpoint values. For the full boundedness promise, even when guards omit some coordinates, distinct signed-core classes of lawful rational points are at sup distance at least $2^{-M}$ with $M\le2^{\operatorname{poly}(L)}$ as given below. A support is rationally inhabited if some lawful rational point has exactly that support. For $n=0$ there is at most one point, and for an empty lawful locus the assertion is vacuous. For $n\ge1$ use the definition of $D_0$ from §1 and put $U=n!D_0^n$. Choose an integer $H\ge1$ such that $|\log_2|c||$ is at most $H$ for every nonzero test coefficient and every positive guard cap is at most $2^H$. For example, let $H$ be one plus the maximum binary length of any numerator magnitude or denominator of a test coefficient or guard cap, using zero for the maximum of an empty list. A nonzero encoded magnitude is then between $2^{-H}$ and $2^H$.

**Upper radius from the input.** Take any rationally inhabited support $S$, and let $G\subseteq S$ consist of its coordinates covered by a guard. Every relevant guard cap is positive. Write $\lambda$ for the vector of log magnitudes in base two. Its active equations are $A_S\lambda=\log_2|c|$, and $\lambda_j\le H$ on $G$. For each $i\in S$, there is no $w$ satisfying

$$
A_Sw=0,\qquad w_j\le0\quad(j\in G),\qquad w_i>0.
$$

Otherwise scale to a rational witness with $w_i\ge1$ by rational feasibility, clear denominators, and evaluate $x_j t^{-w_j}$ at positive rational $t\downarrow0$, starting at a lawful rational point of this support. The active rows remain true, inactive rows remain true because the support is unchanged, and no guarded magnitude increases. The $i$-th magnitude would diverge, contradicting boundedness. Polyhedral Farkas duality yields an expression of $e_i$ as a linear combination of active rows plus a nonnegative combination of the $e_j$ for $j\in G$. Split the free row multipliers into positive and negative parts. A conic representation can use linearly independent generators, by eliminating a dependency while retaining nonnegative coefficients. There are at most $n$ of them. Select a nonsingular square minor and solve by Cramer's rule. The numerator determinants are bounded by $U$ and the nonzero integral denominator has magnitude at least one. Every coefficient is thus at most $U$. Taking the dot product with $\lambda$ proves $\lambda_i\le H n U$. The argument is uniform in the rationally inhabited support, so $2^{H n U}$ is a radius bound computable from the input without finding any chart.

**Lower bound on survivors.** At a terminal support $C\ne\varnothing$, use the theorem of alternatives from §1. Take a basis of independent active rows of rank $k\le n$ and choose multipliers with $v=A_C^{\mathsf T}\mu\ge\mathbf 1$. The polyhedron in these $k$ multipliers has no line, by independence of the rows, so it has a vertex. At a vertex choose $k$ independent incident equalities, solve by Cramer's rule, and multiply all multipliers by the absolute determinant of that square subsystem. This gives integers with $|\mu_j|$ at most $U$, $v_i\ge1$, and $v_i\le n U D_0$. Other row coefficients may be zero. For the lawful representative with support $C$, the coordinate monomials give
$$
\sum_{i\in C} v_i\log_2 |x_i|=\sum_k\mu_k\log_2|c_k|.
$$
The right side is at least $-H n U$. Bounding the other terms above by the upper radius just proved, and using $v_i\ge1$, gives for each survivor
$$
|x_i|\ge 2^{-M},\qquad M=1+H n U+H n^3 U^2 D_0.
$$

The empty core needs no such estimate. A contraction keeps all survivor values, so the lower bound also holds for the survivor coordinates of the original point. If $\|x-y\|_\infty<2^{-M}$, each core support is contained in the intersection of the two original supports. The signs on all their survivor coordinates agree wherever read from the two endpoints. Restrict the two contraction paths to the intersection. They reach the original terminal supports, since these are contained in the intersection. Their common origin and irreducibility imply equality of the two supports, hence equality of the signed cores. This proves the uniform separation and forces every step of smaller mesh to preserve the core. Indeed $\log_2 U\le n(\log_2(n+1)+\log_2 D_0)$ and $M\le 3H(n+1)^3 U^2 D_0$. Thus $M$ has polynomial bit length and can be computed by integer arithmetic on polynomial-size numbers. The denominator of the expanded rational $2^{-M}$ has $M+1$ bits. In the native problem let $N=|X||R|$. Every chain law satisfies the source tests because the held catalogue is monotone. A discrete cover preserves the spectrum, and a fixed-profile rewrite changes each spectral coordinate by at most $2N/\delta$ times the native table distance. The obstruction applies at native tolerance $\delta 2^{-M}/(2N+1)$, computed for the source tests. If $p_A\npreceq p_B$, every tolerance gives a negative answer because each step preserves or advances the profile.

**Repeated-squaring example of Jeronimo, Perrucci and Tsigaridas.** Their Example 13 (published Example 3) with $H=d=2$ and $n+2$ variables gives the following system by identifying the first $n+1$ variables with $x_0,\ldots,x_n$ and the last with $z$. The caps are redundant. Take $x_0=1/2$, $x_{i+1}=x_i^2$ for $i=0,\ldots,n-1$, $z^2=x_n^2$, and coordinate caps one. The two points have identical magnitudes and opposite signs of $z$. Every damping weight is zero by the equations, so the points are distinct cores. Their distance is $2^{1-2^n}$. This excludes every universal lower bound of the form $2^{-\operatorname{poly}(L)}$, since the family has polynomial encoding length in $n$. The signed-core interpretation uses the same two points. To realize this example in the native Markov metric, use a binary base and one shared parity probe, a singleton register, uniform rates fixed by the floor $1/|M|$, self-reversing marks, and a cap $3/4$. Hold calibrations $\alpha_h=1/2$, $\alpha_{x_0}=1/4$, and the two-step equalities $x_{i+1}h\sim x_i x_i$ and $zz\sim x_n x_n$. The corresponding ratios to $\alpha_h$ obey the same repeated squaring, and the two laws differ in a single small signed response. Their native distance is $2^{-2^n-1}/|M|$. All endpoints are lawful. The small-gap bound is in terms of the coordinate list, tests and guards, including the floor when specifying the native instrument, independently of the number of bits required to list a particular endpoint. [Jeronimo, Perrucci and Tsigaridas, Example 13 (published Example 3)](https://arxiv.org/pdf/1112.0544).

## 5. Prior work and scope of the contribution

**Boolean and discrete reconfiguration.** Gopalan, Kolaitis, Maneva and
Papadimitriou prove PSPACE-completeness for two specified 3-CNF solutions
in Lemma 3.6. Their constraint-language approach to Boolean
$s$–$t$ connectivity gives a P/PSPACE-complete boundary, with the
classification corrected by Schwerdtfeger for formulas with constants
and with repeated variables permitted in constraint applications. Safely
tight languages give polynomial time, and the other languages give
PSPACE-completeness.
Schnider and Weber's Definition 1.5 gives the induced cubical complex
used in §2.2, and their Lemma 2.3 establishes projection universality
for 3-SAT. The one-state construction uses that Boolean and cubical
structure, adding the exact rational mesh transfer and the positive-rate
compilation into short measured tests. [Gopalan et al., Lemma 3.6](https://arxiv.org/abs/cs/0609072), [Schwerdtfeger, corrected Theorem 2.9](https://arxiv.org/abs/1312.4524), [Schnider and Weber, Definition 1.5 and Lemma 2.3](https://arxiv.org/abs/2307.03446).

Hearn and Demaine's Corollary 6 supplies the two-orientation AND/OR
graph problem used in §2.1. Their Theorem 9 retains PSPACE-completeness
for planar AND/OR graphs. Cardinal, Demaine, Eppstein, Hearn and
Winslow already prove strong PSPACE-completeness of discrete subset-sum
reconfiguration with one held linear equality and moves affecting at
most three elements (Theorem 3.3). Their lower bound goes through
Sliding Tokens and Exact Cover (Lemma 3.9). Their Theorem 4.7 gives
PSPACE-completeness for single-bit paths through hypercube vertices
satisfying $Ax\le b$, with a constant number of inequalities. Kimura and
Suzuki classify the two-solution problem for integer linear systems
under one-variable changes by the sign-pattern index $Z(I)$. They
obtain constant time for $Z(I)<1$, weak coNP-completeness with a
pseudo-polynomial algorithm for $Z(I)=1$, and PSPACE-completeness for
$Z(I)>1$. [Hearn and Demaine, §2, Corollary 6 and Theorem 9](https://arxiv.org/abs/cs/0205005), [Cardinal et al., Theorems 3.3 and 4.7 and Lemma 3.9](https://arxiv.org/abs/1805.04055), [Kimura and Suzuki, §1](https://arxiv.org/abs/1911.02786).

**Real algebraic reachability.** Bürgisser and Cucker's Proposition 8.15
proves PSPACE-hardness of deciding whether some points of $Z(f,g)$ and
$Z(f,h)$ belong to the same component of the real zero set $Z(f)$, for
integer polynomials $f,g,h$. Remark 8.16 retains the bound for compact
one-dimensional real algebraic sets. Their Lemma 8.14 compiles a
semialgebraic formula to a single equation using square slack variables
and sums of squares for conjunctions. The reachability proof starts
with a symmetric machine configuration graph embedded in a compact
semilinear set by Bürgisser, Cucker and de Naurois (Proposition 5.9,
cited in the proof of Proposition 8.15). Thus hardness on
the real zero set of a single unrestricted polynomial predates the
present result. That source has real components and two polynomially
specified endpoint loci. Here the endpoints are supplied lawful
rational states, and the one-licence restriction concerns measured
word comparisons. [Bürgisser and Cucker, Lemma 8.14, Proposition 8.15 and Remark 8.16](https://arxiv.org/abs/cs/0312007).

Reif proves PSPACE-hardness for the generalized mover's problem for
linked polyhedra in three dimensions, and Canny gives a polynomial
space algorithm for that problem. Hopcroft, Schwartz and Sharir prove
hardness for coordinated motion of rectangles in a rectangular region.
Hopcroft, Joseph and Whitesides prove PSPACE-hardness of moving a
designated joint of a planar linkage to a prescribed point. Alt, Knauer,
Rote and Whitesides prove PSPACE-hardness for planar
tree-linkage reconfiguration between prescribed configurations with
noncrossing constraints (Theorem 2). Basu formulates real two-point
semialgebraic connectivity using roadmaps (§3.1, Definition 3.4) and
discusses PSPACE-hardness of counting components with extension to
quadratic inequalities (§3.6). These results concern real
configuration spaces. [Reif, FOCS 1979](https://hdl.handle.net/1802/13748), [Canny, STOC 1988](https://doi.org/10.1145/62212.62257), [Hopcroft, Schwartz and Sharir, 1984](https://doi.org/10.1177/027836498400300405), [Hopcroft, Joseph and Whitesides, 1984](https://doi.org/10.1137/0213038), [Alt et al., Theorem 2](https://www.cs.mcgill.ca/~sue/papers/unfolding.pdf), [Basu, §§3.1 and 3.6](https://arxiv.org/abs/1409.1534).

**Perturbed dynamics.** Asarin and Bouajjani intersect the reachability
relations for all perturbations of the prescribed dynamics. For their
four models the intersection is co-recursively enumerable, and
ordinary reachability is decidable when it equals that intersection.
For computable Lipschitz discrete-time maps on $[-1,1]^d$, Bournez,
Graça and Hainry prove that the language accepted at every perturbation
scale is co-recursively enumerable (Theorem 1). Blanc and Bournez
characterize PSPACE by polynomial robustness for space-perturbed
Turing machines (Theorem 17). Blanc's Proposition 19 and Corollary 25
give PSPACE-hardness and PSPACE-completeness, respectively, for
`Reach Robust LDL°light`. This problem uses a polynomially robust
discrete-time map in the specified class on a closed rational box,
a closed rational target box, and a unary $p$ specifying the
perturbation scale $2^{-p}$. Her Definitions 2–4 distinguish a fixed perturbation scale, their
intersection, and polynomial robustness. Here the small-step
condition compares successive lawful model parameters directly, using
the prepared marked tables throughout. The reduction supplies its own
distance bound at a specific mesh. [Asarin and Bouajjani, LICS 2001](https://www.irif.fr/~asarin/papers/perturb.pdf), [Bournez, Graça and Hainry, Theorem 1](https://sapientia.ualg.pt/bitstreams/c62dacfb-41f2-4caf-a4ab-e55e9c0d80f5/download), [Blanc and Bournez, Theorem 17 of the preprint](https://arxiv.org/abs/2301.12723), [Blanc, Definitions 2–4, Theorem 5, Proposition 19 and Corollary 25](https://arxiv.org/abs/2610.26206).

Hirahara and Ohsaka obtain constant-factor inapproximability for max-min 3-SAT reconfiguration. Guruswami and coauthors prove the Reconfiguration Inapproximability Hypothesis for constant-arity CSPs. In those results the approximation permits a fraction of constraints to fail at intermediate assignments. Here the tolerance bounds the distance of each step, with every intermediate point satisfying all the constraints. [Hirahara and Ohsaka, §6.1](https://arxiv.org/abs/2401.00474), [Guruswami et al., §3](https://arxiv.org/abs/2312.17140).

**Toric and support algorithms.** Sottile identifies the nonnegative part of the projective toric variety with its polytope through the algebraic moment map (Theorem 8.5). Soprunova and Sottile describe the spherical toric variety as sign copies of the polytope glued using the isotropy subgroup of each face (Proposition 1.3). Theorem 2.1(2) indexes components of the open part $Y^\circ$ of a small cover by the sign group modulo the rank-one isotropy groups. Theorem 2.4(2) indexes components of the spherical toric variety of a full-dimensional lattice polytope by its sign group modulo the subgroup generated by the facet signs. For prescribed signs, those component tests are membership tests in a finite span over $\mathbb F_2$. [Sottile, Theorem 8.5](https://arxiv.org/abs/math/0212044), [Soprunova and Sottile, Proposition 1.3 and Theorems 2.1(2) and 2.4(2)](https://arxiv.org/abs/1102.3045).

Shiu and Sturmfels compute minimal siphons from minimal primes of a binomial ideal (Theorem 3.1) and use saturated ideals to compute relevant minimal siphons (Theorem 3.2). These statements concern boundary supports and their compatibility with invariant polyhedra. Eriksson, Fienberg, Rinaldo and Sullivant characterize existence of the hierarchical log-linear MLE by membership of the observed margins in the relative interior of the marginal cone, with an LP test and a polynomial-time bound for bounded tree width (Theorem 1, Corollary 2 and §3). Adrovic and Verschelde use support selection to parametrize affine complex binomial solution strata (§3). Section 1 uses standard LP, alternatives and gcd-free basis refinement. Its additional result is the iterated support recomputation with signed-core verdicts and two-sided certificates for the bounded, guarded rational binomial problem, including the directed native transfer. [Shiu and Sturmfels, Theorems 3.1 and 3.2](https://arxiv.org/abs/0904.4529), [Eriksson et al., §§2–3](https://arxiv.org/abs/math/0405044), [Adrovic and Verschelde, §3](https://arxiv.org/abs/1405.0320), [Bach, Driscoll and Shallit, J. Algorithms 15 (1993), 199–222](https://doi.org/10.1006/jagm.1993.1038).

**Separation.** Jeronimo, Perrucci and Tsigaridas give an explicit Euclidean separation bound for disjoint connected components of basic closed integer semialgebraic sets when one component is compact (Theorem 2, published Theorem 1.2). Their Example 13 (published Example 3) shows that the double-exponential scale is necessary, and at $H=d=2$ gives the spectral example used in §4. The contribution in §4 is the direct exponent-row bound for the signed-core classes of lawful rational points under rational boundedness, together with its transfer and example in the native Markov metric. [Jeronimo, Perrucci and Tsigaridas, Theorem 2 and Example 13](https://arxiv.org/pdf/1112.0544).

**Probabilistic verification.** Proposition 11 of Junges, Katoen, Pérez and Winkler realizes the affine rescaling $(f+A)/B$ of a polynomial $f$, for sufficiently large $A,B$, as the probability of reaching target states in a parametric Markov chain. Their complexity results concern existence of parameter valuations satisfying reachability thresholds. Parameter synthesis and model repair likewise address satisfying valuations or regions. Gainer, Hahn and Schewe reuse state elimination to compute target-reachability probabilities as a Markov chain is reconfigured. In the full audited problem an edit chain runs through lawful states with laws and profiles, and covers can add held tests. In the one-state lower-bound construction, the profile and short positive-rate tests stay fixed, and each state is determined by its rate vector. The finite-event expressivity theorem in the manuscript's Appendix B supplies the unrestricted balanced-suffix gadget used in §3. [Junges et al., Proposition 11](https://arxiv.org/pdf/2009.13128#page=30), [Junges et al., Parameter Synthesis for Markov Models](https://doi.org/10.1007/s10703-023-00442-x), [Češka et al., §1](https://arxiv.org/abs/2105.13411), [Gainer, Hahn and Schewe, §§2–3](https://arxiv.org/abs/1804.01872).

**Rational solvability.** The source question in §3 is Hilbert's tenth problem over the rationals in its standard polynomial-root formulation. Mazur's programme studies the real closure of rational points. Cornelissen and Zahidi prove that Mazur's conjecture would rule out a Diophantine model of $\mathbb Z$ in $\mathbb Q$. The supporting proposition in §3 uses local arithmetic gates and a denominator-zero obstruction to put the existence of a rational root into a chain problem with two supplied lawful endpoints. An October 2026 preprint claims undecidability of Hilbert's tenth problem over the rationals, and Sun reports that claim in his introduction. Its status here is a reported, independently unverified claim. The proposition is a many-one reduction whose proof is independent of that report. [Poonen, §10](https://math.mit.edu/~poonen/papers/aws2003.pdf), [Mazur, Experimental Mathematics 1 (1992), 35–45](https://doi.org/10.1080/10586458.1992.10504244), [Cornelissen and Zahidi, main theorem](https://arxiv.org/abs/math/0006140), [October 2026 preprint](https://github.com/openai/math/tree/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026), [Sun, §1](https://arxiv.org/abs/2610.20691).

**Scope of the contribution.** The
claim is delimited by the literature searches behind the paper's related-work
section. The comparison of joint endpoint
tables through their uniform and probe coefficients is the character
calculus of the instrument. One widened licence contributes one mass
equation and one equation per probe, so the number of scalar equations
can grow with the input. The added result uses those simultaneous
equations and the existing response budgets to encode NCL in the
restricted measured syntax, with exact rational fine reachability and
hardness at the supplied mesh. Its polynomial-time counterpart is the
iterated signed-core algorithm and two-sided certificates for the same
instrument with single-word licences.

A matching upper bound for rational fine reachability with exactly
one two-word licence remains open here. The exactly-one restriction in
the probe-free one-state subclass also remains open, even for fixed
publication-free profiles with a positive rate floor and arbitrary
equal positive word durations within each licence. The one-state
proposition in §2.2 allows a growing number of two-word licences.
The single-equality compression in §3 allows events of growing
cardinality and duration. The [bounded-probe follow-up](BoundedProbes.md)
proves two polynomial-time fragments without probes and reduces the
remaining no-probe question to a closure of feasible rational ratios.
Its rational-solvability reduction uses exactly one short two-word
licence with a growing probe set.

## 6. Lean correspondence

The headline uses `EventExperiments` for both arms. It keeps the native fields and names and gives each licence an optional second word on the right, constrained by the same positive duration and horizon as its primary pair. Singleton licences use the native compilation. For a two-word licence the native compilation receives a reflexive pair, and legality imposes the actual joint-mass comparison separately. Attained profiles use this full legality predicate. The singleton embedding preserves the complete state and chain relation,
including covers, and every all-singleton instrument has that form.
The construction in §2.1 constructs an instance of the same type from a
constraint-logic network, with one widened catalogue entry and a policy
holding the full catalogue. The supporting Boolean compiler in §2.2 uses
the named-licence one-state construction, which preserves chain existence at
each tolerance. The same one-state construction applies to the arithmetic
compiler's two-step catalogue in §3.

The auxiliary one-state model used for the compiler and supporting results is a fixed-profile subtype of the native protocol, restricted by external joint-mass predicates. Its underlying instrument has empty licence and publication types and its horizon field is two. It uses actual `Protocol.Step` with the original metric. The external predicates admit arbitrary word lists, so that field does not govern the longer singleton or compressed tests. For the unrestricted compression in §3, the written experiment replaces the named catalogue, policy and held sets together and supplies the adequate duration bound from the words. Lean checks the rate-preserving state bijection, step equivalence, and equivalence of chain existence at every tolerance between the two auxiliary predicates. For the generated short and compressed tests, both events are nonempty and their measured probability is positive. The positive masses give the one-state conditional-licence interpretation. Generic empty events remain joint-mass predicates, and an empty word, where admitted by the generic singleton type, has mass one.

| Result | Checked endpoint and scope |
| --- | --- |
| Shared audited instrument | [`NativeExperiments.singleton_joint_iff`, `EventExperiments.licensed_joint_mass` and `chain_ofNative_iff`](MovingProjection/EventExperiments.lean) identify the measured licence semantics and preserve the original singleton chain relation at every tolerance, including covers. [`eq_ofNative_of_singletons`](MovingProjection/ComplexityTheorem.lean) identifies every all-singleton instrument with its canonical embedding. |
| Joint headline | [`EventExperiments.complexity_boundary`](MovingProjection/ComplexityTheorem.lean) states the full singleton criterion and certificate soundness and completeness on presented inputs, together with the restricted NCL reduction at the supplied tolerance and for fine reachability. |
| Headline singleton-word arm | [`singleton_criterion` and `singleton_certificate`](MovingProjection/ComplexityTheorem.lean) give the signed-core criterion and accepted certificates for the full original instrument class viewed in the common language. |
| Single-word lower bound | [`Circuit.native_fine_iff_value`](MovingProjection/MonotoneCircuitMarkov.lean) checks the monotone circuit reduction using the full native laws and edits. [`Encoding.checked_reduction`](MovingProjection/MonotoneCircuitEncoding.lean) transfers it to the common language and checks the bounded record stream. The source hardness and ordinary tape simulation are given in the [written reduction](SingleWordHardness.md). |
| Headline exactly-one arm | [`joint_words_iff`, `ncl_exactly_one`, `ncl_licence_duration`, `ncl_base_size`, `ncl_chain_iff`, `ncl_fine_iff` and `ncl_endpoints_distinct`](MovingProjection/SingleAdditiveLicence.lean) give the probe equations, restrictions, base size and both reduction directions in the common language. [Detailed correspondence](SingleAdditiveLicence.md#6-lean-correspondence). |
| Supporting one-state hardness | [`widened_chain_iff`](MovingProjection/WidenedOneState.lean) proves equivalence of chain existence at every tolerance between the named-licence instance and the one-state model used in the compiler. [`widened_fine_iff_flips`, `widened_chain_iff_flips_of_le` and `widened_endpoints_distinct`](MovingProjection/ComplexityTheorem.lean) prove the resulting equivalences and distinctness of endpoints in the common language. |
| Contraction and strict-dual checker | [`checkCore_sound`](MovingProjection/CoreCertificate.lean) proves correctness for an accepted supplied witness. [`checkCore_complete_short`](MovingProjection/CertificateComplete.lean) proves that one exists, with at most one stage per removed coordinate. |
| Native directed verdict | [`ProfileTable.leCheck_correct`, `nativeCheck_sound` and `nativeCheck_complete`](MovingProjection/NativeCertificate.lean) cover the profile comparison and the executable checker on the source's compiled rows. The endpoint type `Presented` carries legality, including the policy premise. |
| Quantitative obstruction | [`dual_log_identity`, `dual_survivor_lower` and `Protocol.signature_eq_of_bounded_mesh`](MovingProjection/CoreGap.lean) give the identity, a magnitude estimate given an accepted dual and numerical bounds, and the native obstruction given a uniform survivor bound. |
| Measured short tests and native metric | [`native_word_mass`, `native_test_holds_iff`, `native_event_step_iff` and `native_event_chain_iff`](MovingProjection/NativeEvents.lean) check the joint masses and identify the restricted native steps and chains with rate steps and chains. |
| Two-step compiler | [`mark_card`, `tests_length`, `tests_ne_nil`, `encode_lawful`, `lawful_decode` and `fine_encode_iff`](MovingProjection/EventCompiler.lean) prove the counts, nonemptiness, both lawful translations, uniqueness of the lift and mesh transfer. The Lean test list uses a noncomputable enumeration of finite sets. |
| Boolean reduction | [`native_chain_iff_flips_of_le`, `native_fine_iff_flips` and `endpoints_distinct`](MovingProjection/BooleanEvents.lean) start with a tautology-free formula and satisfying assignments. They prove the iff at each $0<\varepsilon\le2r$ and for fine reachability. Distinct assignments give distinct lawful endpoints. |
| Supporting rational-root proposition | [`native_chain_iff_solvable_of_le`, `native_fine_iff_solvable` and `endpoints_distinct`](MovingProjection/ArithmeticEvents.lean) check the gated reduction for supplied gate lists, with distinct lawful endpoints. [`solvable_iff_zero`, `native_chain_iff_rational_zero_of_le` and `native_fine_iff_rational_zero`](MovingProjection/PolynomialEvents.lean) check evaluation and both chain equivalences for a supplied arithmetic term. |
| One held equality | [`outputWord_injective`, `event_card_add_le`, `event_word_length`, `measured_event_pos`, `measured_test_iff`, `event_probability_iff`, `compressedEquiv`, `compressedEquiv_rate`, `compressed_step_iff` and `compressed_chain_iff`](MovingProjection/FiniteEventCompression.lean) check the occurrence encoding, positive masses for a nonempty catalogue, faithfulness of the measured test, a rate-preserving bijection of auxiliary states, step equivalence, and equivalence of chain existence at every tolerance. |
| Tractable event restrictions | [`one_step_event_fine` and `singleton_event_fine`](MovingProjection/NativeTractable.lean) give a native chain at every positive tolerance for lawful endpoints under the respective predicates. The duration-one predicate adds only linear event equalities. Singleton tests carry equal duration and a positive ratio. |

The general binary encoding and size analysis, exact LP search and running time, and numerical witness bit bounds are written proofs. Section 1 also gives raw binomial endpoint validation, prepared-table readout on promised lawful native inputs and serialization of the compiled rows. The executable certificate check takes the source rows and both endpoint tables and laws, with candidate contraction certificates for the branch that passes the profile comparison. Its soundness and completeness use two presented lawful states. Lean proves soundness, certificate existence and the stage count independently of how the witness was obtained. The project has no verified bit-cost model, rational LP solver or gcd-free basis algorithm.

The exactly-one arm imports Hearn and Demaine's hardness theorem on paper.
Lean checks the full semantic network reduction, including the binary basis,
with explicit polynomial enumeration and bit-time accounting on paper.
The written Boolean reduction invokes Gopalan and coauthors' PSPACE-completeness theorem, deletes tautologies, and handles equal input endpoints before applying the compiler. Lean starts with the preprocessed formula and its satisfying endpoints. The width-three size calculation is on paper. For the arithmetic source the polynomial-time claim uses a sparse-binary input and shared straight-line gates on paper. The Lean semantic proof for a term traverses its finite expression tree before deduplicating subterms. It is an evaluation correctness result, with the gate-list equivalence proved separately.

The determinant derivation of the uniform input-only threshold, the repeated-squaring examples, the real-fiber path-connectivity assertion, and the interpretation of the generated short and compressed tests as fixed-profile experiments with a sufficient horizon and a positive-mass conditional endpoint law are written proofs. The Lean results certify the rational predicates, measured masses and chain equivalences for both headline arms and the fixed-profile auxiliary models. The quantitative Lean chain result takes the uniform survivor bound that §4 derives.
