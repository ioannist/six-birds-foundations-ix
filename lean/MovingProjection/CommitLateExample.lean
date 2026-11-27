import MovingProjection.CommitLate

/-! A duration-two singleton licence that is safe to acquire only after
crossing a zero of an uncommitted probe response. -/

namespace MovingProjection.CommitLateExample

open scoped BigOperators

abbrev Profile := Capabilities Bool Bool Unit Unit Unit 0

def parity : ParityBasis Unit Bool where
  value _ x := if x then 1 else -1
  abs_eq_one _ x := by cases x <;> norm_num
  balance _ := by simp
  orthogonal i j := by cases i; cases j; norm_num [Fintype.sum_bool]

def instrument : NativeExperiments Bool Unit Bool Unit Unit Unit where
  parity := parity
  weights := fun _ => 1
  weights_pos := fun _ => by norm_num
  weights_unit := by simp
  reversal := id
  reversal_involutive := fun _ => rfl
  δ := 1/2
  κ := 1/2
  δ_pos := by norm_num
  κ_lt_one := by norm_num
  horizon := 2
  license := fun _ => ⟨false, true, [false], [true], rfl, le_rfl⟩
  audit := fun _ => .calibration true () (1/4)
  policy := fun _ => True

noncomputable abbrev D := instrument.protocol
abbrev State := D.State 0

def profile (held : Bool) : Profile :=
  ⟨OrderDual.toDual Set.univ, fun _ => OrderDual.toDual ⊤,
    if held then {()} else ∅, {()}⟩

def law (x : ℚ) : PhysicalLaw Bool Unit Bool Unit :=
  ⟨fun _ => 1/2, fun mi => if mi.1 then 1/4 else x, fun _ _ _ _ _ => 1⟩

private theorem law_legal (held : Bool) (x : ℚ) (hx : |x| ≤ 1/2)
    (hh : held = true → x*x = (1/4 : ℚ)*(1/4)) :
    D.legal (profile held) (law x) := by
  refine ⟨fun _ _ _ => le_rfl, trivial, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ⟨fun _ => le_rfl, by norm_num [law, Fintype.sum_bool], ?_⟩
    intro r hr
    change r ∈ D.checks.rateTests (profile held).licenses {()} at hr
    simp only [ProbeCatalog.rateTests, List.mem_append, List.mem_flatMap] at hr
    rcases hr with ⟨g, _, h⟩ | ⟨g, _, h⟩
    · change r ∈ [⟨routeRateRow [false,false] [true,true],1⟩] at h
      obtain rfl := List.mem_singleton.mp h
      exact (route_rate_compile _ _ _ _).2 (by norm_num [law])
    · cases h
  · refine ⟨?_, ?_⟩
    · intro r hr
      change r ∈ D.checks.spectralTests (profile held).licenses {()} at hr
      simp only [ProbeCatalog.spectralTests, List.mem_append, List.mem_flatMap,
        Finset.mem_toList] at hr
      rcases hr with (h | ⟨g,hg,h⟩) | ⟨a,_,h⟩
      · change r ∈ Finset.univ.toList.map (reversalTest id) at h
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
        simp [MonomialTest.holds, reversalTest]
      · have hh' : held = true := by cases held <;> simp_all [profile]
        change r ∈ Finset.univ.toList.map
          (routeCharacterTest [false,false] [true,true]) at h
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
        let s (m : Bool) (_ : Unit) : ℚ := if m then 1/4 else x
        change monomial (characterExponent [false,false] i) (fun mi => s mi.1 mi.2) =
          1 * monomial (characterExponent [true,true] i) (fun mi => s mi.1 mi.2)
        rw [character_monomial, character_monomial]
        simpa [s] using hh hh'
      · change r ∈ [calibrationTest true () (1/4)] at h
        obtain rfl := List.mem_singleton.mp h
        change monomial (pointExponent ((true : Bool), ())) (law x).spectrum =
          1/4 * monomial (fun _ => 0) (law x).spectrum
        rw [pointMonomial]
        norm_num [monomial, law]
    · intro cap hc
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp hc
      change (∑ i : Unit, |(law x).spectrum (m,i)|) ≤ 1/2
      cases m
      · simpa [law] using hx
      · norm_num [law]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [law, instrument, Protocol.fiber, NativeExperiments.protocol]
  · ext e
    simp [registerMask, Protocol.fiber, profile, law]

private def unheld (x : ℚ) (h : |x| ≤ 1/2) : State :=
  ⟨profile false, law x, law_legal false x h (fun h => by cases h)⟩

private def held (x : ℚ) (h : |x| ≤ 1/2)
    (h' : x*x = (1/4 : ℚ)*(1/4)) : State :=
  ⟨profile true, law x, law_legal true x h (fun _ => h')⟩

def source : State := unheld (1/4) (by norm_num)
def early : State := held (1/4) (by norm_num) (by norm_num)
def throughZero : State := unheld 0 (by norm_num)
def beforeCommitment : State := unheld (-1/4) (by norm_num)
def target : State := held (-1/4) (by norm_num) (by norm_num)

private theorem commitment_cover : D.CapCover (profile false) (profile true) := by
  have hle : profile false ≤ profile true :=
    Capabilities.le_coordinates.2 ⟨fun _ h => h, fun _ => le_rfl,
      Finset.empty_subset _, fun _ h => h⟩
  have hne : profile false ≠ profile true := by
    intro he
    have h := congrArg Capabilities.licenses he
    simp [profile] at h
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro r _ hr hs
  obtain ⟨hm₁,hg₁,_,ha₁⟩ := Capabilities.le_coordinates.1 hr.le
  obtain ⟨hm₂,hg₂,_,ha₂⟩ := Capabilities.le_coordinates.1 hs.le
  have hm : r.mask = (profile false).mask := Set.Subset.antisymm hm₁ hm₂
  have hg : r.grades = (profile false).grades :=
    funext fun j => le_antisymm (hg₂ j) (hg₁ j)
  have ha : r.published = (profile false).published := Finset.Subset.antisymm ha₂ ha₁
  by_cases h : () ∈ r.licenses
  · apply hs.ne
    exact Capabilities.ext hm hg (Finset.Subset.antisymm (by
      intro i _
      cases i
      simp [profile]) (by simpa [profile] using h)) ha
  · apply hr.ne
    exact (Capabilities.ext hm hg (Finset.eq_empty_iff_forall_notMem.2 (by
      intro i
      cases i
      exact h)) ha).symm

theorem early_acquisition (ε : ℚ) : D.Step ε .route source early := by
  exact ⟨commitment_cover, ⟨rfl,rfl,commitment_cover.1.ne.imp (fun h => Capabilities.ext rfl rfl h rfl),rfl⟩, rfl⟩

theorem late_acquisition (ε : ℚ) : D.Step ε .route beforeCommitment target := by
  exact ⟨commitment_cover, ⟨rfl,rfl,commitment_cover.1.ne.imp (fun h => Capabilities.ext rfl rfl h rfl),rfl⟩, rfl⟩

/-- Acquiring the licence preserves the law, but the reverse direction
would remove a held licence and violates profile monotonicity. -/
theorem early_to_source_no_chain (ε : ℚ) : ¬ D.Chain ε early source :=
  fun h => (not_le_of_gt commitment_cover.1) (Protocol.Chain.profile_le h)

private theorem marked_diag (s : State) :
    s.law.marked parity false (false,()) (false,()) =
      (1 + s.law.spectrum (false,())) / 4 := by
  have hfloor := s.legal.2.2.1.1
  have h₁ : (1/2 : ℚ) ≤ s.law.rate false := hfloor false
  have h₂ : (1/2 : ℚ) ≤ s.law.rate true := hfloor true
  have hsum : s.law.rate false + s.law.rate true = 1 := by
    simpa [Fintype.sum_bool, add_comm] using s.legal.2.2.1.2.1
  have hr : s.law.rate false = 1/2 := by linarith
  have hreg : s.law.register false false false () () = 1 := by
    simpa using s.legal.2.2.2.2.1.2.1 false false false ()
  simp [PhysicalLaw.marked, nativeMarked, hr, hreg, ParityBasis.kernel, parity,
    Fintype.card_bool]
  ring

private theorem branch (s : State) (hp : s.profile = profile true) :
    s.law.spectrum (false,()) = 1/4 ∨ s.law.spectrum (false,()) = -1/4 := by
  have hcal : s.law.spectrum (true,()) = 1/4 :=
    instrument.calibration_value s (e := ()) (by rw [hp]; simp [profile]) rfl
  have h := (instrument.license_measured s (g := ()) (by rw [hp]; simp [profile])).2
  have h' := (parity.word_identity_iff (fun m i => s.law.spectrum (m,i))
    false true [false] [true]).1 h ()
  simp only [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
    mul_one, hcal] at h'
  have hh : (s.law.spectrum (false,()) - 1/4) * (s.law.spectrum (false,()) + 1/4) = 0 :=
    by linear_combination h'
  rcases mul_eq_zero.mp hh with hh | hh
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

private theorem marked_near {x y ε : ℚ} (hε : 0 < ε) (h : |x-y| / 4 < ε) :
    PhysicalNear parity ε (law x) (law y) := by
  obtain ⟨h₁,h₂⟩ := abs_lt.mp ((div_lt_iff₀ (by norm_num : (0 : ℚ) < 4)).1 h)
  rintro m ⟨a, u⟩ ⟨b, v⟩
  cases m <;> cases a <;> cases b <;>
    norm_num [PhysicalLaw.marked, nativeMarked, ParityBasis.kernel, parity, law,
      Fintype.card_bool, abs_lt] <;> (first | exact hε | constructor <;> linarith)

set_option maxHeartbeats 500000 in
theorem late_numerical_through_zero (ε : ℚ) (hε : 0 < ε) :
    D.Chain ε source throughZero ∧ D.Chain ε throughZero beforeCommitment := by
  obtain ⟨M,hM⟩ := exists_nat_gt (1/(8*ε))
  let N := 2*M
  have hN : 1/(8*ε) < (N : ℚ) := hM.trans_le (by
    simp only [N, Nat.cast_mul, Nat.cast_ofNat]
    have hM₀ : (0 : ℚ) ≤ M := by positivity
    linarith)
  have hNp : 0 < (N : ℚ) := (by positivity : (0 : ℚ) < 1/(8*ε)).trans hN
  have hstep : 1 / (8*(N : ℚ)) < ε := by
    have hh := (div_lt_iff₀ (show 0 < 8*ε by positivity)).mp hN
    apply (div_lt_iff₀ (show 0 < 8*(N : ℚ) by positivity)).2
    linarith only [hh]
  let x (k : ℕ) : ℚ := 1/4 - (k : ℚ) / (2*(N : ℚ))
  have hbound (k : ℕ) (hk : k ≤ N) : |x k| ≤ 1/2 := by
    have hdiv : (k : ℚ) / (2*(N : ℚ)) ≤ 1/2 := by
      apply (div_le_iff₀ (show 0 < 2*(N : ℚ) by positivity)).2
      have : (k : ℚ) ≤ N := by exact_mod_cast hk
      linarith
    have hdiv' : 0 ≤ (k : ℚ) / (2*(N : ℚ)) := by positivity
    rw [abs_le]
    unfold x
    constructor <;> linarith
  let node (k : ℕ) (hk : k ≤ N) := unheld (x k) (hbound k hk)
  have hchain (i k : ℕ) (hik : i ≤ k) (hi : i ≤ N) :
      ∀ hk : k ≤ N, D.Chain ε (node i hi) (node k hk) := by
    induction k, hik using Nat.le_induction with
    | base => intro _; exact .refl
    | succ k hik ih =>
      intro hk
      have hk' : k ≤ N := (Nat.le_succ k).trans hk
      apply (ih hk').tail
      refine ⟨.rewrite, ?_⟩
      refine ⟨rfl, marked_near hε ?_⟩
      have he : x k - x (k+1) = 1 / (2*(N : ℚ)) := by
        simp only [x, Nat.cast_add, Nat.cast_one]
        ring
      rw [he, abs_of_pos (by positivity)]
      convert hstep using 1
      ring
  have hhalf : M ≤ N := by dsimp [N]; omega
  have hx0 : x 0 = 1/4 := by simp [x]
  have hxM : x M = 0 := by
    have hMp : (0 : ℚ) < M := (by positivity : (0 : ℚ) < 1/(8*ε)).trans hM
    simp only [x, N, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  have hxN : x N = -1/4 := by unfold x; field_simp; ring
  have hfirst : node 0 (Nat.zero_le N) = source := by
    unfold node source
    congr
  have hmid : node M hhalf = throughZero := by
    unfold node throughZero
    congr
  have hlast : node N le_rfl = beforeCommitment := by
    unfold node beforeCommitment
    congr
  exact ⟨hfirst ▸ hmid ▸ hchain 0 M (Nat.zero_le M) (Nat.zero_le N) hhalf,
    hmid ▸ hlast ▸ hchain M N hhalf hhalf le_rfl⟩

theorem late_numerical : D.Factorable source beforeCommitment :=
  fun ε hε =>
    let h := late_numerical_through_zero ε hε
    h.1.trans h.2

theorem late_factorable : D.Factorable source target :=
  fun ε hε => (late_numerical ε hε).tail ⟨.route, late_acquisition ε⟩

theorem early_chain_iff (ε : ℚ) : D.Chain ε early target ↔ 1/8 < ε := by
  constructor
  · intro hc
    by_contra! hε
    have stays (s : State) (h : D.Chain ε early s) (hp : s.profile ≤ profile true) :
        s.law.spectrum (false,()) = 1/4 := by
      induction h with
      | refl => rfl
      | @tail s t hs hstep ih =>
        rcases hstep with ⟨eff,he⟩
        have hs' : s.profile = profile true := le_antisymm (he.profile_le.trans hp) (Protocol.Chain.profile_le hs)
        have ht' : t.profile = profile true := le_antisymm hp ((Protocol.Chain.profile_le hs).trans he.profile_le)
        have hsrc := ih hs'.le
        have hr : eff = .rewrite := by
          by_contra hn
          simp only [Protocol.Step, if_neg hn] at he
          exact he.1.1.ne (hs'.trans ht'.symm)
        subst eff
        have hnear : PhysicalNear parity ε s.law t.law := he.2
        rcases branch t ht' with ht | ht
        · exact ht
        · have h := hnear false (false,()) (false,())
          rw [marked_diag, marked_diag, hsrc, ht] at h
          norm_num at h
          linarith
    have h := stays target hc le_rfl
    norm_num [target, held, law] at h
  · intro hε
    apply Relation.ReflTransGen.single
    refine ⟨.rewrite, rfl, marked_near (by linarith) ?_⟩
    norm_num
    exact hε

theorem early_not_factorable : ¬ D.Factorable early target :=
  fun h => (lt_irrefl (1/8 : ℚ)) ((early_chain_iff (1/8)).1 (h _ (by norm_num)))

end MovingProjection.CommitLateExample
