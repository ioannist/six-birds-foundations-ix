# The effect of timing a held test

## Statement

Write $A\leadsto B$ if for every positive rational tolerance $\varepsilon$ a finite lawful edit chain goes from $A$ to $B$. A commitment is an attained profile cover that adds one named licence or publication, leaving the support, grades and physical law unchanged. Compare three lawful states in the same instrument:

- $A=(p,L)$ before the commitment,
- $A^+=(q,L)$ immediately after that same commitment,
- $B=(r,L_B)$ at the destination, with $q\le r$.

The immediate and delayed cases use the same test and the same physical endpoints. In particular, the law at $A$ already passes the new test. The comparison asks whether $A\leadsto B$ and $A^+\not\leadsto B$.

**Timing theorem.** This strict difference occurs in the single-word instrument of Theorem 2.1 with two base states, two marks, one probe, a singleton register, one existing calibration, and one new duration-two licence. In the full instrument with single-word and two-word comparisons, the difference holds exactly when the two projected marked tables lie in the same connected component before the acquisition and in different connected components after it. In each comparison the space is the closure of the projected tables of the *lawful rational states at that profile*. For single-word licences the corresponding test is equality of the two signed cores computed at $p$ and inequality of the two signed cores computed at $q$.

More precisely, put
$$
J(L)_{mxy}=\theta_m K_{\alpha_m}(x,y),\qquad
K_p=\overline{\{J(H): (p,H)\text{ is a lawful rational state}\}}
\subseteq \mathbb R^{M\times X\times X}.
$$
Use the sup metric on tables and write $u\sim_p v$ for membership in the same connected component of $K_p$. If $p\le q$ are attained, $K_q\subseteq K_p$. For a source profile $p$ and target profile $r$, first check $p\le r$. If it fails, profile monotonicity excludes every edit chain. When $p\le r$, the criterion is
$$
(p,L)\leadsto(r,L_B)\quad\Longleftrightarrow\quad J(L)\sim_p J(L_B).
\tag{1}
$$
Thus the timing difference is precisely
$$
J(L)\sim_p J(L_B)\quad\text{and}\quad J(L)\not\sim_q J(L_B).
\tag{2}
$$
This identifies the component of the stronger test space in which it is safe to commit relative to a specified target. Both endpoint laws pass the added test. The source law must also legally admit the proposed cover. The destination can have smaller support. Attainment includes the instrument's licence policy.

The order condition in (1) is essential even when the projected tables are identical. In the example below, a chain from $A^+$ back to $A$ would remove the held licence, so every tolerance rules out that direction.

## Proof for the full instrument

**Transfer of rates and probe responses.** A state supplies a rational law $(\theta,\alpha,T)$ with a register $T$ and with its measured support and grade conditions. If $u$ is an attained profile, choose any lawful template at $u$. If the licences and publications at $u$ are subsets of those at a state $s$, combine the template's register with the rates and probe responses of $s$. The rate floor, normalization, reversal identities and response budgets carry over. The compiled single-word and publication equations at $u$ are a subset of those satisfied at $s$. For each timed word $w$, the joint probability of $w$ and projected endpoint $y$, prepared at $(x,a)$, is
$$
\left(\prod_{m\text{ in }w}\theta_m\right)
K_{\alpha_{w_1}}\cdots K_{\alpha_{w_{|w|}}}(x,y).
$$
This is the prepared trajectory factorization in `nativeWordEndpoint_factor`, obtained by summing the row-stochastic register at each step. It depends only on $\theta,\alpha$. Therefore every held comparison with a two-word side carries over as well. The template register still has the required support, reciprocity and grade. This proves legality of the combination. In particular, for $p\le q$ attained, every lawful rational projected table at $q$ occurs at $p$, which gives the claimed inclusion of closures.

**Relation between the two metrics.** For any prepared register value $a$, the projected entry is the sum of the full marked entries over the $|R|$ possible output register values. If all the full-entry differences are strictly less than $\eta>0$, each projected difference is strictly less than $|R|\eta$. Conversely, if projected differences are strictly less than $\varepsilon>0$, lifting both laws with one common register gives full differences strictly less than $\varepsilon$: each difference is multiplied by a register entry in $[0,1]$. A cover preserves $\theta,\alpha$ and hence preserves $J$.

**Fixed numerical values allow profile advancement.** Suppose two lawful states carry the same $\theta,\alpha$ and the source profile is at most the target profile. Take a saturated chain in the finite interval of attained profiles between them. At each intermediate profile choose an attained register and combine it with the destination's $\theta,\alpha$ by the first step of the proof. On a cover that changes support, the equality of rates and probe responses is exactly the condition for a cover edit. On a cover with equal support, the upper law is legal at the lower profile. Its tests imply the lower tests, and a register satisfying the upper grades satisfies the coarser lower grades with the same support. Replace the lower state's register by the upper register at the lower profile, then take the cover with its full law fixed. This register replacement uses affine rational interpolation. All register equations and inequalities are affine, and a convex combination of nonnegative entries with common positive support has that same support. The word tests are independent of the register. At fixed rates and responses the full table is entrywise linear in the register, so a rational mesh makes the full steps small enough for any given tolerance. The same argument applies when the initial and final profiles coincide. Concatenation gives fine reachability at the fixed numerical values from the lower to the upper attained profile.

**Reduction to the source profile.** Given a full lawful chain from $A$ to $B$, carry every state back to $p$ with the original source register, using the first step of the proof. All profiles along the chain are above $p$. The projections of cover edits become equal states. The projection of an $\eta$-rewrite is an $\varepsilon$-rewrite if $|R|\eta\le\varepsilon$. For each rational $\varepsilon>0$, apply the assumed fine reachability with $\eta=\varepsilon/(|R|+1)$. The result is a chain at $p$ to the state with the target's $\theta,\alpha$ and the source register. Conversely, append the fixed-numerical-value chain to $B$ to any such source-profile chain. In particular, for any attained intermediate profile between $p$ and $r$, one can visit it with the target's rates and responses, then proceed to $B$. If the intermediate profile has the target support, the entire target law is legal there and can be used at that profile. An entire prescribed chain of attained profiles can be visited after the rate and probe-response revisions by using the same construction on each successive pair. The later phase can include register rewrites. If the prescribed steps add only named tests, this applies to every acquisition order whose prescribed profiles are attained.

**Compact components.** The projected rational tables lie in $[0,1]^{M\times X\times X}$, since the rates are positive and sum to one and each projected kernel is stochastic. Their closure is compact. For a dense subset $H$ of a compact metric space $K$, two points of $H$ admit finite chains in $H$ with all step lengths less than every positive tolerance if and only if they lie in the same connected component of $K$. For necessity use the compact Hausdorff theorem that a component is the intersection of the clopen neighbourhoods of its point. A clopen set separating the endpoints and its complement are disjoint compact sets at positive distance, so a sufficiently fine chain cannot leave the set. For sufficiency, fix $\varepsilon>0$ and take the unions of open $\varepsilon/3$ balls centered at points of $H$ that are, respectively, reachable and unreachable from the start by an $\varepsilon$-chain. The unions cover the component by density. An intersection would give two centers less than $2\varepsilon/3$ apart and contradict the way the centers were partitioned. If the target were unreachable the two disjoint open sets would disconnect the component.

At a fixed attained profile, full fine chains project to arbitrarily fine chains on the rational projected set by the first metric bound. Choose positive rational tolerances as small as needed for a prescribed real tolerance. Conversely, lift a rational projected chain using the fixed source register, then interpolate the register to the desired endpoint register at fixed rates and probe responses. For each projected point one can take any lawful rational state realizing it. The last point can be realized using the desired endpoint's rates and responses and the source register, so the interpolation starts with the correct numerical values. This proves the fixed-profile statement. The source-profile reduction proves (1), and applying (1) twice gives (2). The inclusion $K_q\subseteq K_p$ implies that each new component lies in an old component. The obstruction is exactly the splitting of the old component on the pair of endpoints.

In the single-word instrument, apply Theorem 2.1 first at $p$ and then at $q$. The profile comparisons are already given, and $A$ and $A^+$ have the same spectra. The resulting criterion is
$$
\operatorname{SCore}_p(\alpha_L)=\operatorname{SCore}_p(\alpha_{L_B}),
\qquad
\operatorname{SCore}_q(\alpha_L)\ne\operatorname{SCore}_q(\alpha_{L_B}).
$$
For explicitly encoded single-word instruments the existing polynomial-time algorithm and certificates apply to both comparisons, with the input endpoints lawful and the proposed commitment admissible. For widened licences the compact-component statement is a characterization. Computing the components of the closure of the rational projected tables is a separate problem. The distinction from using the full real solution set is substantive in this instrument, as the single-probe example in [BoundedProbes.md](BoundedProbes.md) shows.

## Explicit single-word instance

Let $X=\{0,1\}$, with one probe $\chi(0)=-1$, $\chi(1)=1$, and let the register have one value. The two marks are $a,b$, with identity reversal. Set the rate floor and absolute-response cap both to $1/2$, and allow both licence profiles. Since the two rates sum to one, $\theta_a=\theta_b=1/2$ in every lawful state. The singleton register's only entry is one. Use full support and the unique grade. Publish the calibration $\alpha_b=1/4$ at both profiles. The horizon is two, with the only named licence
$$
aa\ \;\text{and}\; bb\quad\text{have equal prepared projected word laws}.
$$
Both words have mass $1/4$. On the probe they have eigenvalues $\alpha_a^2$ and $\alpha_b^2$, so the licence is equivalent to $\alpha_a^2=\alpha_b^2$. With the calibration held, taking it on restricts $\alpha_a$ to $\{1/4,-1/4\}$.

Take $A$ with $\alpha_a=1/4$ and the licence unheld. Take $B$ with $\alpha_a=-1/4$ and the licence held. The calibration, cap, positivity, reversal and register conditions hold for both endpoints, and either law qualifies at either profile. Adding the one licence is an attained cover and keeps the law fixed, so it can be taken on at either endpoint.

To delay, leave the licence unheld and choose an even integer $N>1/(8\varepsilon)$. Use the successive rational responses
$$
\alpha_a(k)=\frac14-\frac{k}{2N},\qquad k=0,\ldots,N.
$$
The midpoint $k=N/2$ has response zero. The budget holds throughout, and the published probe stays calibrated. The prepared marked table at mark $a$ has entries $(1+\alpha_a\chi(x)\chi(y))/4$, while the table at $b$ is fixed. Each step therefore has sup length $1/(8N)<\varepsilon$. Acquire the licence at the final law. This proves fine reachability by chains with the commitment last.

For early acquisition, take the licence at $A$ and call the new state $A^+$. From $A^+$ to $B$ the endpoint profiles agree. Every intermediate profile must be this same profile by monotonicity. Every lawful intermediate response $\alpha_a$ is one of the two allowed values. A sign switch changes the prepared diagonal entry for mark $a$ from $5/16$ to $3/16$, a difference of $1/8$. Thus no chain exists at any $0<\varepsilon\le 1/8$. For $\varepsilon>1/8$, a single rewrite takes $A^+$ to $B$: the two full tables have sup distance exactly $1/8$. The obstruction is the loss of the intervening response values, including zero, when the licence is held. A finite coarse chain can jump across the gap, whereas the fine-reachability definition requires chains at every tolerance.

## Literature check and attribution

The abstract mechanism is established in adjacent settings. Gopalan, Kolaitis, Maneva and Papadimitriou define the solution graph as the subgraph of the Hamming cube induced by the satisfying assignments. Conjoining another predicate induces a further subgraph, which can separate two surviving vertices. In multimodal motion planning, Hauser and Latombe §2.3 require a transition to pass through the intersection of the old and new feasible sets, and explicitly observe that a nonempty intersection does not suffice for a path because the transition point can lie in a different component. Section 2.5 further discusses separation on either side of the transition. Hu, Iyer and Christensen §IV.B likewise use motions constrained to individual manifolds between their intersections. These are precedents for restricting a feasible space and selecting a feasible commitment point. [Gopalan et al., solution graph definition](https://arxiv.org/abs/cs/0609072) · [Hauser and Latombe, *Multi-Modal Motion Planning in Non-Expansive Spaces*, §§2.3–2.5](https://ai.stanford.edu/~khauser/papers/wafr08-multimodal.pdf) · [Hu, Iyer and Christensen, §IV.B](https://arxiv.org/abs/2310.08494)

The Markov-model repair problem in Češka et al. §1 asks for a revised model satisfying a probabilistic specification, including options to vary support. It does not impose a chain of exact intermediate tests on the path from the source to a fixed destination model. Soprunova and Sottile's Proposition 1.3 and Theorem 2.4 analyze sign gluing and components of spherical toric varieties. The singleton criterion above applies Theorem 2.1 to two held-test catalogues and inherits its mathematical dependencies. [Češka et al., §1](https://arxiv.org/abs/2105.13411) · [Soprunova and Sottile](https://arxiv.org/abs/1102.3045)

Paperclip arXiv searches on restriction and connectivity (`s_ee310926`), Markov revision and exact calibration (`s_e904d8b4`), and staged constraint activation (`s_bb357701`) found the adjacent work above. An exact-title Paperclip lookup for Hauser and Latombe (`s_342480e3`) returned citing papers without the requested paper, which was then checked in the authors' PDF. A narrower search for delayed commitment in rational Markov revision (`s_a752b62c`) returned model-checking results about trajectories within a process. The checked work supplies precedents for the geometric mechanism. The search did not locate the full projected-rational characterization for the Foundations IX instrument, the result that all rate and probe-response revisions can run under the source profile even with later support changes, or this calibrated marked-word instance. This is a scoped comparison to the checked sources.

## Lean correspondence

| Written step | Checked declarations |
| --- | --- |
| Changing the register and carrying the old tests, including widened ones | `EventExperiments.carry`, `EventExperiments.atSource` in [CommitLate.lean](MovingProjection/CommitLate.lean) |
| The two metric bounds | `EventExperiments.projected_near`, `EventExperiments.carry_near` |
| Register interpolation and the fixed-numerical-value profile phase | `EventExperiments.fixedProfile_registerChain`, `EventExperiments.chain_of_sameNumbers` |
| Source-profile reduction and target-value scheduling | `EventExperiments.factorable_iff_atSource`, `EventExperiments.commitAtTargetNumbers`, `EventExperiments.commitAtTarget`, `EventExperiments.commitAtTargetNumbersAlong` |
| The compact metric lemma, nested closures, (1) and (2) | `fineMesh_iff_component`, `EventExperiments.projectedClosure_mono`, `EventExperiments.fixedProfile_iff_projectedComponent`, `EventExperiments.factorable_iff_projectedComponent`, `EventExperiments.commitLate_iff_projectedComponents` in [CommitLateComponents.lean](MovingProjection/CommitLateComponents.lean). `EventExperiments.Chain.profile_le` in [EventExperiments.lean](MovingProjection/EventExperiments.lean) rules out chains when $p\le r$ fails. |
| The signed-core timing test | `NativeExperiments.commitLate_iff` in [CommitLate.lean](MovingProjection/CommitLate.lean), using `NativeExperiments.exact_six_iff` |
| Lawful endpoints, both forward acquisitions, reverse-order rejection, the mesh through zero, and the exact early threshold | `CommitLateExample.source`, `early`, `throughZero`, `beforeCommitment`, `target`, `early_acquisition`, `late_acquisition`, `early_to_source_no_chain`, `late_numerical_through_zero`, `late_numerical`, `late_factorable`, `early_chain_iff`, `early_not_factorable` in [CommitLateExample.lean](MovingProjection/CommitLateExample.lean) |

The formalization uses the existing Markov instrument types and edit relations. Lean checks the mathematical implications, the concrete instance and the compact-component argument. The literature comparison is written. The polynomial-time timing decision runs the single-word reachability algorithm once at each starting profile. The algorithm computes and compares the two endpoints' signed cores in each run. The algorithmic proofs for these computations, certificate construction and verification, and the associated running-time and bit bounds are on paper. The existing Lean theorems give soundness of the checker and existence of certificates. [ComplexityBoundary.md](ComplexityBoundary.md)

Verification used `cd lean && lake build MovingProjection`. The axiom audit of the timing theorems, scheduling results and explicit instance found only `propext`, `Classical.choice` and `Quot.sound`.
