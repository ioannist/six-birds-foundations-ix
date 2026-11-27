# Empty cores, refinement and closure

This note proves three facts about the signed core. The native statements use the full single-word instrument of Theorem 2.1. For the support calculus we use arbitrary finite lists of exponent rows, including on supports that have no lawful realization.

Fix a finite coordinate set $J$. Write $C_R(S)$ for the least reduct of $S\subseteq J$ under the rows $R$. A row is active on $S$ when all its positive exponents on both sides belong to $S$. A contraction uses nonnegative integer weights, zero outside $S$, that give both sides of every active row the same weighted degree. It removes exactly the positive-weight coordinates. The active rows are recomputed after each contraction. The signed core of a sign code $s$ keeps its original signs on $C_R(\operatorname{supp}s)$ and sets all other entries to zero.

## 1. When the core is empty

**Contraction calculus.** If the active rows at $S$ admit a damping vector that is strictly positive on all of $S$, one contraction reaches the empty support. In particular, if every active row has equal total degrees on the two sides, use weight one on $S$ and zero elsewhere. Each active row has zero exponents outside $S$, so its weighted degree is its total degree. The strongest support-level criterion, including cases that need successive contractions, is
$$
C_R(S)=\varnothing
\quad\Longleftrightarrow\quad
S\text{ contains no nonempty irreducible sub-support}.
$$
This follows from §3. For two lawful rational spectra with empty cores, rational realization gives a fine chain from each to the zero spectrum. Concatenate the first chain with the reverse of the second. This implication uses no boundedness hypothesis.

**Why the native hypothesis matters.** The test $(xy)^2=xy$ is an allowed monomial test in the abstract calculus. It has neither a constant monomial nor a point calibration, and the zero spectrum passes. Put the guard $|x|+|y|\le 2$ and use the lawful endpoints $(1,1)$ and $(-1,-1)$. On the full support both sides are nonzero, so $xy=1$. The damping equation $2w_x+2w_y=w_x+w_y$ forces both weights to be zero. The full support is irreducible and is the core at both endpoints. Their signed cores are $(+,+)$ and $(-,-)$. The guard bounds both coordinates, so the signed-core necessity theorem rules out fine connectivity. Thus absence of a nonzero point calibration alone gives no empty-core guarantee for arbitrary monomial tests.

**The full native instrument.** Let $p$ be any profile and let a rational spectrum pass its compiled spectral tests. Its signed core at $p$ is zero **if and only if** $p$ holds no calibration to a nonzero value. This applies to the spectrum of a lawful state at $p$ and to the spectrum of a lawful target at any profile $r$ with $p\preceq r$.

For sufficiency, a licence compares equal-duration words. At each probe, the degree of a word monomial is the sum of its mark counts, hence the word length. All such rows are homogeneous, as are reversal rows, which compare one coordinate to one coordinate. Rate-ratio publications add only rate equations. A zero calibration $\alpha_{m,i}=0$ makes that coordinate absent in every passing spectrum, so its row is inactive on the support. The active rows are therefore balanced and the supported all-ones damping deletes the whole support.

For necessity, a nonzero calibration forces its coordinate to belong to the support. On the singleton containing that coordinate, the point-calibration row is active and forces its weight to zero. The singleton is irreducible. By §3 it lies in the core of any support containing it. In particular every held nonzero calibration contributes its coordinate to every lawful core. This proof uses the passing-test condition even for a zero calibration. For an exact counterexample without that condition, take the two-mark instrument of §2 with the calibration changed to $\alpha_b=0$ and the licence unheld. The all-zero spectrum makes the profile attained. The formal singleton consisting of the $b$ response has itself as core, but no lawful state at that profile has that support.

Now start at any lawful state $A$ with no nonzero calibration at its profile $p_A$. Every lawful target $B$ with $p_A\preceq p_B$ passes the source spectral tests by inclusion of both catalogues. Both source-relative signed cores are zero. Theorem 2.1 yields fine reachability. In the other direction each edit preserves or advances the profile. Thus for this source, fine reachability is equivalent to the directed condition $p_A\preceq p_B$. The all-zero spectrum is also a lawful state at $p_A$ with the same rates and register, mutually finely reachable with $A$. The zero spectrum gives the uniform conditional base kernel at each mark. The rate and register data can still differ between states.

## 2. Adding tests refines the classes

**Contraction calculus.** Suppose every row of $R$ occurs in $R'$. Any $R'$-contraction is an $R$-contraction with the same weights, source and destination. This holds with the active rows recalculated at each intermediate support, so every $R'$-reduction is an $R$-reduction. By leastness, $C_R(S)\subseteq C_{R'}(S)$. In fact both compositions satisfy
$$
C_R(C_{R'}(S))=C_R(S)=C_{R'}(C_R(S)).
$$
The first equality is invariance under reduction, applied to the stronger core as a reduct in the weaker calculus. For the second equality, deflation gives the inclusion into $C_R(S)$, and row monotonicity and idempotence give the reverse inclusion. These identities hold also for signed cores. The support of a signed core is exactly the corresponding support core, and any coordinate retained by either composition has its original sign. Consequently equality of stronger signed cores implies equality of weaker ones.

For lawful rational points, every fine chain holding more tests is also a fine chain holding the original tests, with the same guards and distances. Therefore, on the states that still pass all tests, each stronger class lies inside one original class. A new test can also remove states from consideration altogether. This implication follows directly by forgetting tests and requires neither boundedness nor the signed-core classification.

**The full native instrument.** If $p\preceq q$, the licences and publications are nested, so their compiled spectral row lists are nested by membership. For any two spectra, equality of their signatures at $q$ implies equality at $p$. More generally, take lawful sources $A,A'$ with $p_A\preceq p_{A'}$ and the same spectrum. For any lawful target $B$, fine reachability from $A'$ implies $p_{A'}\preceq p_B$ and equality of the signatures computed at $p_{A'}$. Directed order is transitive, and forgetting rows gives equality at $p_A$. Theorem 2.1 yields fine reachability from $A$. In particular this applies when a lawful acquisition leaves the full source law fixed.

**Strict example.** Use the two-mark instrument of [CommitLate.md](CommitLate.md#explicit-single-word-instance). The sole publication is $\alpha_b=1/4$. Before holding $aa\sim bb$, the core of any support containing $b$ is $\{b\}$: the calibration fixes its weight at zero and damping weight one on $a$, if present, removes $a$. Identity reversal contributes only tautological rows. After holding $aa\sim bb$ the full support has the additional weight equation $2w_a=2w_b$. Together with $w_b=0$, this forces $w_a=0$ and makes the full support irreducible. Both laws $(\alpha_a,\alpha_b)=(\pm1/4,1/4)$ pass the test, with the same full supports throughout this comparison of endpoint laws. They are finely connected before acquisition and separated at native tolerance $1/8$ after acquisition. Their old signed cores agree, while the new ones differ in the $a$ sign. At the old profile the whole signed core is the positive sign at $b$ for every spectrum passing the calibration. Thus a nonzero calibration is compatible with fine reachability to every lawful target above that source profile.

## 3. Which map is a closure

**Support order.** Every reduct is a subset of its starting support, so $C_R(S)\subseteq S$. Applying the core again gives the same support, by invariance under reduction. If $U\subseteq S$, the reduction $S\to^*C_R(S)$ restricts to a reduction $U\to^*U\cap C_R(S)$. Leastness gives $C_R(U)\subseteq U\cap C_R(S)\subseteq C_R(S)$. Hence $C_R$ is a monotone, deflationary, idempotent map, that is, an **interior operator** for inclusion. Equivalently, it is a closure operator in reverse inclusion. Deflation can be strict on an attained support: the old two-mark core in §2 drops $a$ from $\{a,b\}$. So $C_R$ itself fails the extensive law for ordinary inclusion.

**Removed coordinates.** On the subsets $Z\subseteq J$ of a fixed universe $J$, define
$$
\operatorname{Cl}_R(Z)=J\setminus C_R(J\setminus Z).
$$
Complementation in $J$ reverses inclusion and is an involution. It carries monotonicity and idempotence to the new map and converts deflation into extensivity. This gives the closure operator in the report. Its closed sets are exactly the complements in $J$ of the irreducible supports.

**Irreducible sub-supports.** A support is irreducible exactly when it has no proper one-step contraction. Then every reduction from it stays there, so it is fixed by $C_R$. Conversely, a fixed support is contained in every reduct of itself, and each reduct is also a subset of it. By idempotence $C_R(S)$ is itself irreducible. For any irreducible $U\subseteq S$, support monotonicity gives $U=C_R(U)\subseteq C_R(S)$. Thus $C_R(S)$ is the **greatest** irreducible sub-support of $S$, and in particular it is the union of all irreducible sub-supports of $S$. The formula ranges over all sub-supports, whether or not they occur as intermediate stages of any particular reduction.

**Attained native supports.** At a fixed profile, start with a lawful state of spectral support $S$. The rational realization of contractions gives a lawful spectrum with support $C_R(S)$ and the original values on this support. Combine it with the rates and register of the original law, which already meet the other requirements of this profile. Fine connectivity of the two spectra gives equal signed cores under the bounded response budgets. Theorem 2.1 makes the resulting state mutually finely reachable with the original state at the same profile. Thus the interior operator restricts to attained supports, and the core is the greatest irreducible sub-support even if one restricts the candidates to attained supports. The closure on deleted coordinates is available on the whole finite coordinate universe. Attainment is needed when interpreting the complement as a hypothetical law.

## Lean correspondence

| Step | Declaration |
| --- | --- |
| (1), support criterion and rational chains through zero | `core_eq_empty_iff`, `core_eq_empty_of_positive_damping`, `core_eq_empty_of_balanced_active`, `fineConnected_of_empty_cores` in [CoreOrder.lean](MovingProjection/CoreOrder.lean) |
| (1), balanced native rows, exact calibration criterion and directed reachability | `NativeExperiments.active_spectral_rows_balanced`, `calibration_mem_core`, `NativeExperiments.spectral_core_empty_iff`, `NativeExperiments.signature_eq_zero_iff`, `NativeExperiments.factorable_iff_profile_le_of_no_nonzero_calibration`, `NativeExperiments.realise_zero_of_no_nonzero_calibration` in [NativeCoreOrder.lean](MovingProjection/NativeCoreOrder.lean) |
| (2), forgetting rows, both absorption identities, and refinement | `Contracts.of_rows_subset`, `Reduces.of_rows_subset`, `core_mono_rows`, `core_absorb_rows`, `signedCore_absorb_rows`, `signedCore_eq_of_rows_subset`, `FineConnected.of_tests_subset` in [CoreOrder.lean](MovingProjection/CoreOrder.lean). `Protocol.spectralRows_mono`, `Protocol.signature_eq_of_profile_le`, `NativeExperiments.factorable_of_higher_source` in [NativeCoreOrder.lean](MovingProjection/NativeCoreOrder.lean) |
| (3), closure, interior and greatest irreducible sub-support | `coreInterior`, `removedClosure`, `removedClosure_isClosed_iff`, `irreducibleSupport_iff_core_eq`, `core_greatest_irreducible`, `core_eq_union_irreducible` in [CoreOrder.lean](MovingProjection/CoreOrder.lean) |
| (3), lawful realization and restriction to attained supports | `NativeExperiments.realise_core`, `NativeExperiments.attainedCoreInterior`, `NativeExperiments.core_greatest_attained_irreducible` in [NativeCoreOrder.lean](MovingProjection/NativeCoreOrder.lean) |
| Examples | `CoreOrderExamples.product_legal`, `product_zero_legal`, `product_core`, `product_not_fineConnected`, `Native.zero_calibration_formal_support`, `Native.strict_core_growth`, `Native.strict_reachability_split`, `Native.calibration_alone_no_obstruction`, `Native.core_not_extensive_on_attained_supports` in [CoreOrderExamples.lean](MovingProjection/CoreOrderExamples.lean) |

The full `lake build MovingProjection` passes. The main implications, bundled order operators and concrete examples were audited for axioms. The audit found only `propext`, `Classical.choice` and `Quot.sound`.
