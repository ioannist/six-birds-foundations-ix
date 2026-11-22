# An audited Markov example requiring two contractions

A time-two route test pins a projected response at $+1/4$ until a different response reaches zero. The two endpoint laws have the same signed core, even though one contraction cannot reach that core and the initially active damping equations would separate the endpoints. The rational path below realizes the connection independently of the classification theorem.

## Instrument and held tests

Use the two parity states $b\in\{0,1\}$, with $\chi(b)=(-1)^b$, and a four-cell register $R=\{0,1,2,3\}$. Mark $m\in\{0,1,2,3\}$ has probability $1/4$, is its own reverse, and has projected transition kernel

$$
Q_m(b,c)=\frac{1+a_m\chi(b)\chi(c)}{2},
\qquad (a_0,a_1,a_2,a_3)=(x,y,z,0).
$$

All responses stay in $[-1/2,1/2]$. The marked native probability from $(b,u)$ to $(c,v)$ is $(1/4)Q_m(b,c)L_m(b,c;u,v)$. Use the same coupled register as in the omission example. Its entries are $1/4$ except on $m=2,\ b=c=0,\ u,v\in\{0,1\}$, where the $2\times2$ submatrix is diagonal with diagonal $1/2$. Every conditional register row and column sums to one. Symmetry gives reversibility with uniform stationary mass, and each disclosed block $\{0,1\}$ or $\{2,3\}$ has conditional mass $1/2$ from every preparation. Both grades disclose this partition. All $Q_m$ entries are positive, so the native support is fixed by $L$ throughout.

Hold the license comparing the marked words $[0,1]$ and $[0,2]$, and publish the calibration $z=1/4$. After summing out the final register, the native word endpoint probabilities for every prepared cell and observed parity endpoint are

$$
\frac{1}{16}\frac{1+xy\,\chi(b)\chi(c)}{2}
\quad\text{and}\quad
\frac{1}{16}\frac{1+xz\,\chi(b)\chi(c)}{2}.
$$

The license therefore requires $xy=xz$. The signed native calibration signal is $(1/4)z=1/16$. These two held tests give $y=1/4$ whenever $x\ne0$. With $x=0$, both word endpoint probabilities are $1/32$ for each observed parity endpoint, regardless of $y$.

## Explicit edits and core calculation

With $z=1/4$ throughout, follow three rational affine segments in $(x,y)$,

$$
(1/4,1/4)\ \longrightarrow\ (0,1/4)\ \longrightarrow\ (0,0)\ \longrightarrow\ (0,-1/4).
$$

For a segment whose varying coordinate runs from $a$ to $b$, given any rational tolerance $\varepsilon>0$, take an integer $N>\lvert b-a\rvert/\varepsilon$ with $N\ge1$. Sample the coordinate at $a+(b-a)k/N$ for $k=0,\ldots,N$. Each sample satisfies the rate floor, response budget, register and disclosure conditions, route license, and publication. A change in any marked native entry has magnitude at most the change in the varying coordinate, hence strictly less than $\varepsilon$ at every step. The mark-1 probability of retaining the prepared parity, conditional on the mark, goes from $5/8$ to $3/8$.

The reversal rows of the compiled spectral tests are identities. The calibration row enforces $w_z=0$ at every support containing $z$.

| Current support | Active word balance | Permitted contraction used |
| --- | --- | --- |
| $\{x,y,z\}$ | $w_x+w_y=w_x+w_z$, so $w_y=0$ | Set $w_x=1$ and $w_y=w_z=0$ |
| $\{y,z\}$ | Inactive after $x$ vanishes on both sides | Set $w_y=1$ and $w_z=0$ |
| $\{z\}$ | Inactive | The calibration forces $z$ to survive |

The first support cannot contract directly to $\{z\}$, since every admissible first contraction retains $y$. It also cannot contract directly to the target sign pattern, since the retained $y$ keeps its initial positive sign. The negative endpoint has support $\{y,z\}$ and can contract to $\{z\}$ using the second row of the table. Thus the signed core is $+1$ at $z$ and zero elsewhere for both endpoints. The general signed-core theorem predicts factorability, and the explicit rational edits realize that prediction in the marked native probabilities.

Freezing the initial activity test keeps the balance $w_y=w_z=0$ at every subsequent support. Every frozen signed reduct of either endpoint retains its original sign at $y$. The endpoints therefore have no common frozen signed reduct, even though the native rewrite chains connect them at every positive tolerance. The route equality is still held along the whole chain. Its rule for which damping equations apply changes when $x$ vanishes.

## Lean

In [`MovingProjection.StagedContraction`](MovingProjection/StagedContraction.lean), `pins_response`, `held_trajectories` and `fixed_audit_signal` identify the measured constraints. `edits_through_zero` constructs the three rewrite chains at every positive rational tolerance. `physical_support_held` identifies the fixed native support. `route_inactive_of_gate_zero` establishes inactivity at every sample with a zero gate response. `two_contractions`, `no_single_contraction_to_core`, `no_single_contraction_to_target_sign` and `signed_cores` compute the dynamic reduction. `factorable_by_signed_core` applies the general classification and `frozen_rejects` proves the opposite frozen verdict.
