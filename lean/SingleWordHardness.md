# P-completeness of single-word fine reachability

## The strengthened boundary

Take the explicitly presented measured instruments of the [complexity boundary theorem](ComplexityBoundary.md) and supply two lawful rational endpoint states. Fine reachability asks for a finite lawful edit chain at every positive rational tolerance.

1. **Single-word licences.** Fine reachability is **P-complete under deterministic log-space many-one reductions** on this input promise. The reductions produce lawful inputs on both yes and no instances. The established polynomial-time signed-core decision and polynomial-size, polynomial-time checkable certificates for both answers apply. Hardness holds with a binary base, one parity probe, one register value, grade zero, full support, identity mark reversal, horizon three, all words of length exactly three, response cap $1/2$, and just one held nonzero calibration, equal to $1/4$. All licences are held at both endpoints, at the same profile within each instance. The policy admits exactly this one licence set. With $n$ circuit gates the reduction uses $n+2$ equally likely marks, floors their rates at $1/(n+2)$, and supplies endpoints differing only by the sign of a single response of magnitude $1/4$.
2. **Exactly one two-word licence.** Fine reachability is **PSPACE-hard under polynomial-time many-one reductions** when one licence compares a single word with two distinct words and every other licence compares single words. The existing reduction holds with a common fixed profile, all licences held, a singleton register, grade zero, full support, identity reversal, cap $1/2$, and distinct lawful rational endpoints. Its unique widened licence can have duration one or duration two, with every other licence of duration three. Its hardness also holds for chain existence at a supplied positive inverse-polynomial tolerance. The construction uses one probe per NCL edge and one reserve probe. [Exactly-one-licence proof](SingleAdditiveLicence.md) · [Duration-one sharpening](BoundedProbes.md#1-duration-one-in-the-hardness-construction)

For the first arm, the complexity statement is about the promised-lawful inputs of the existing theorem. Equivalently, any polynomial-time decision language that agrees on that promise is P-complete. The reduction imposes no validity-checking assumption on the decision algorithm. The binary base and single probe are restrictions for the P-hardness construction.

## 1. Source problem and lawful native endpoints

Use monotone circuit value with a numbered list of $n\ge1$ gates, a specified output gate $o$, and gates of type constant $0$, constant $1$, binary AND, or binary OR. Each predecessor index is smaller than the current index. Binary inputs may repeat. The source is P-complete under deterministic log-space reductions by Goldschlager. His proof uses earlier numbered predecessors and supplies a truth assignment to the input variables. Replacing each input occurrence by its assigned constant uses a scan of the assignment and an index counter. If needed, let the distinguished output be the last gate, or use its explicit index. [Goldschlager, monotone circuit value theorem](https://doi.org/10.1145/1008354.1008356)

Use one mark for each gate and two fresh marks $z,s$. Denote each mark's unique spectral response by the same symbol as the mark when writing a row equation. The base is $\{0,1\}$, with the balanced probe $\chi(0)=-1$ and $\chi(1)=1$. The register has one value with weight one. Each conditional register entry is one, so row sums, stationarity, reciprocity and the sole disclosed partition hold. Set the response cap to $1/2$. Give every mark rate $1/(n+2)$ and set the floor to this same number. The floor and normalization force these rates in every lawful state of every attained profile of the instrument. Reversal fixes every mark.

Publish the calibration $z=1/4$. As in the referee's change 1, a comparison with common factors guards equality of the remaining factors. Here the shorter comparisons are padded with $z$ so that every timed word has three letters. The table gives the two named licence slots for each gate $y$ with predecessors $a,b$.

| Gate | Slot 0 | Slot 1 |
| --- | --- | --- |
| Constant 0 | $yzz\sim zzz$ | $yzz\sim zzz$ |
| Constant 1 | $zzz\sim zzz$ | $zzz\sim zzz$ |
| AND | $yaz\sim zaz$ | $ybz\sim zbz$ |
| OR | $yab\sim zab$ | $yab\sim zab$ |

The duplicate and reflexive comparisons simplify the indexing of the named catalogue. A licence name identifies a comparison, and the single-word model permits these rows. One final licence is $sso\sim zzo$, with $o$ denoting the output mark. This gives exactly $2n+1$ names. The policy consists of the one set of all these names. At the common endpoint profile, hold all of them and the calibration. The register support and partition are identical at both endpoints.

For $A$ set every response to $1/4$. For $B$ set the response at $s$ to $-1/4$ and leave the others at $1/4$. All three-letter words have the same rate product. All gate tests agree on the response products at both endpoints, since only the sentinel sign changes and no gate test uses it. In the output test the sentinel appears twice, so its sign does not change the response product there either. The calibration and cap hold. The measured word compilation therefore proves that both states are lawful, regardless of the circuit value. Their difference at the sentinel proves they are distinct. Positivity of the base kernels and the unit register give the stated support.

## 2. The core computes the circuit

In a support containing both sides of a word comparison, the corresponding damping equation equates the sums of weights over the words, counting repetitions. Common factors contribute equal terms to the two sums. Thus any active gate row with head $y$ equates $w_y$ and $w_z$. For the constant-1 dummy row this equality is $w_z=w_z$. An active output row equates $2w_s$ and $2w_z$, hence $w_s=w_z$. Whenever $z$ is present, its calibration requires $w_z=0$. Identity reversal contributes no constraint to the weights.

Both endpoints have full spectral support. Let $K$ be its support core and let $F$ consist of $z$, the false circuit gates, and $s$ if the output is false. We show $K=F$.

**False gates survive.** At support $F$, the calibration is active. Every false gate has an active pinning row. A constant 0 has its $z$-guarded row. A false AND gate has a false predecessor, giving an active row in that predecessor's slot. A false OR gate has both predecessors false, so its row is active. If the sentinel belongs to $F$, the output gate is false and also belongs to $F$, so the output row is active. These rows force all weights on $F$ to be zero. So $F$ is irreducible. The greatest-irreducible-sub-support theorem gives $F\subseteq K$.

**True gates are absent.** Induct in the listed order. Suppose a true gate $y$ belongs to $K$. In a true constant's slots the rows are tautologies. In a true AND, both predecessors are true and absent from $K$ by induction, so each guarded row for $y$ is inactive. In a true OR, some true predecessor is absent and the row using both factors is inactive. Give $y$ weight one and every other coordinate weight zero. The calibration and the other gate rows balance, because any use of $y$ as a guard contributes equally on both sides. The output row also balances when $y$ occurs as its guard. This is an admissible damping supported on $K$ and it deletes $y$, contradicting irreducibility of $K$. So every true gate is absent. If the output is true, its absence makes the sentinel's row inactive. If the sentinel were present, the corresponding singleton damping would now delete it. Thus $K\subseteq F$ as well.

The signs on every surviving coordinate agree between $A$ and $B$ except for $s$ if it survives. The profiles coincide. By the native signed-core reachability theorem,
$$
A\leadsto_{\rm fine}B
\quad\Longleftrightarrow\quad s\notin K
\quad\Longleftrightarrow\quad \text{the circuit output is true}.
$$
In particular the reduction does not compute any gate value in order to set the endpoint states. Only the proof computes the core by reference to those values.

## 3. Deterministic logarithmic-space transduction

Number $z,s$ by $0,1$ and gate $i$ by $i+2$, taking the source list to be zero-indexed. Number the output comparison by $0$ and slot $b\in\{0,1\}$ of gate $i$ by $1+2i+b$. These numberings give distinct names within the two tables. One explicit output representation uses the following records, with binary natural fields separated by delimiters. Delimiters and any other fixed alphabet symbols can be replaced by fixed binary codes.

- A header records $n+2$ marks, two base values, one register value, one probe, horizon three, floor $1/(n+2)$, cap $1/2$, $2n+1$ licence names and one calibration.
- A fixed geometry record gives the signed entries of the probe, the register weight, grade zero, the sole partition and the fact that the policy lists just one admissible set.
- A mark record gives the name, its reverse, the common endpoint rate, and the two signed responses. It also gives the four unit conditional register entries and the four support bits, in the fixed order of the base pairs. The endpoint rate, register and support values that agree can be printed twice if the target grammar requires separate tables.
- A licence record gives its name and the two triples of mark IDs, followed by three membership bits, all one. The bits list membership in the one admissible set and in the two endpoint licence sets. The calibration record gives the mark $0$, probe $0$, value $1/4$ and two held flags. Thus the policy is an explicit list of one set, even in a presentation that does not accept a predicate describing admissible sets.

The order is the header, geometry, the mark records, the output licence, the two slots of each numbered gate in source order, and the calibration. There are $3n+6$ records, at most seventeen fields per record, and every field is smaller than $2n+16$. Sharing identical entries between the endpoints in this representation just abbreviates two explicit copies. Sequential rescans and counters expand such a representation to separately listed fields, including partitions, support bits, and the sorted lists of policy and held names. If prepared marked tables are requested, each entry is $3/(8(n+2))$ or $5/(8(n+2))$. The probe signs and the negative-sentinel flag determine which. Their reduced forms also have logarithmic bit length.

For an input of length $L$, first count the gate records and read the distinguished output index. A mark record uses only $n$ and a counter for its mark ID. For a gate slot, scan to the indicated gate record, read its tag and at most two predecessor indices, and compute the mark and licence IDs using addition and doubling. Reuse the same workspace at the next request. In particular, the work tape holds a constant number of fields or counters for the input position, the current record and slot, the header data, the current gate record, and the current output record and bit. These have $O(\log(L+2))$ bits. Binary output of one natural field can scan its bits from the highest nonzero bit down, with a bit-index counter, before writing the delimiter. The records are written directly to the output tape. Counting the input size, parsing or rescanning, and the fixed-depth arithmetic take polynomial time with this workspace. The output length is $O((n+1)\log(n+2))$ bits. For a total reduction, validate the source list and backward indices in preliminary scans and send malformed inputs to the fixed negative instance from a one-gate circuit with output 0. Large malformed numbers can be rejected as soon as they exceed the input-length bound for valid IDs. The scans use logarithmic space also on malformed inputs.

[MonotoneCircuitEncoding.lean](MovingProjection/MonotoneCircuitEncoding.lean) implements the record requests with the distinguished output in the header and a read-only indexed gate reader. Its gate branch reads only the requested gate. A single bounded cursor controls the stepping function, which emits one record, advances the cursor, and halts after exactly $3n+6$ records. Lean checks the licence word records against the instrument's word pairs, the endpoint rate and spectrum formulas, the cursor transitions, and the logarithmic width bounds for both fields and cursor. Lean does not decode mark records or the full stream: the field interpretation, the full serialization correspondence with the instrument and endpoints, and the tape implementation are written-only. The previous paragraph implements that indexed access by scans of a read-only input tape and accounts for the work tape and bit output. It is the machine-level part of the written proof.

Combining this transduction with Goldschlager's theorem proves P-hardness. The established upper bound in [ComplexityBoundary.md](ComplexityBoundary.md#1-proof-of-the-polynomial-time-arm) computes the two signed cores by polynomial-size linear programming and checks the directed profile comparison. Its certificates apply to both verdicts. This proves the P-complete arm at the stated strength.

## Lean correspondence

| Written step | Lean check |
| --- | --- |
| Listed gates, truth, timed pairs and fixed measured instrument | `Circuit.value`, `Circuit.gatePair`, `Circuit.outputPair`, `Circuit.licence_duration_three`, `Circuit.instrument` in [MonotoneCircuitMarkov.lean](MovingProjection/MonotoneCircuitMarkov.lean) |
| Lawful endpoints and compiled rows | `Circuit.endpoint_legal`, `Circuit.endpoint`, `Circuit.licence_row`, `Circuit.calibration_row`, `Circuit.row_cases` |
| Exact false-gate and true-gate argument, then fine reachability | `Circuit.survivors_irreducible`, `Circuit.true_wire_absent`, `Circuit.true_output_sentinel_absent`, `Circuit.remaining_eq_survivors`, `Circuit.native_fine_iff_value`, `Circuit.endpoints_distinct` |
| The explicit emitter, correspondence and finite resource bounds | `emit`, `step_matches_stream`, `step_halts`, `output_record_correct`, `gate_record_correct`, `mark_record_correct`, `stream_length`, `fields_fit_bits`, `cursor_fits_bits`, `checked_reduction` in [MonotoneCircuitEncoding.lean](MovingProjection/MonotoneCircuitEncoding.lean) |
| Established selector gadget for the widened case and certificates in the single-word case | `EventExperiments.complexity_boundary` in [ComplexityTheorem.lean](MovingProjection/ComplexityTheorem.lean) |

The checked reduction takes any well-formed topologically listed circuit and constructs the lawful endpoints without any hypothesis about their fine reachability or signs. The standard source hardness theorem and the complexity-class conclusions are used in the written proof. The ordinary tape implementation is also proved in writing from the checked bounded-cursor transducer and indexed read operations. Lean checks the semantic reduction and the local record construction and bounds, with no imported complexity-class axiom.
