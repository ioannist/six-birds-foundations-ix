import MovingProjection.EventExperiments
import MovingProjection.NativeEvents

/-! The two-step compiler's fixed-profile states are a subclass of the
widened audited instrument. Each test becomes a named license and the
policy holds the full catalogue. -/

namespace MovingProjection.OneStateEvents

open scoped BigOperators

variable {M : Type} [Fintype M] [DecidableEq M]

private def wordList (w : Word M) : List M := [w.1, w.2]

private def timed (l r : Word M) : TimedPair M 2 :=
  ⟨l.1, r.1, [l.2], [r.2], rfl, le_rfl⟩

private def testPair : Test M → TimedPair M 2
  | .equal l r => timed l r
  | .sum l r _ _ => timed l r

private def testSecond : (t : Test M) → Option (SecondWord (testPair t))
  | .equal _ _ => none
  | .sum _ r w h => some
    ⟨wordList w, rfl, fun he => h (by
      have hs : wordList w = wordList r := he
      simpa [wordList, Prod.ext_iff] using hs.symm)⟩

def widened (tests : List (Test M)) (floor : ℚ) (hf : 0 < floor) :
    EventExperiments M Empty Unit Unit (Fin tests.length) Empty where
  native := {
    parity := singletonParity
    weights := fun _ => 1
    weights_pos := fun _ => by norm_num
    weights_unit := by simp
    reversal := id
    reversal_involutive := fun _ => rfl
    δ := floor
    δ_pos := hf
    κ := 0
    κ_lt_one := zero_lt_one
    horizon := 2
    license := fun i => testPair (tests.get i)
    audit := fun i => i.elim
    policy := fun held => held = Finset.univ
  }
  second i := testSecond (tests.get i)

abbrev WidenedState (tests : List (Test M)) (floor : ℚ) (hf : 0 < floor) :=
  (widened tests floor hf).State 0

private def wideProfile (tests : List (Test M)) : Capabilities M Unit Unit (Fin tests.length) Empty 0 :=
  ⟨OrderDual.toDual Set.univ, fun _ => OrderDual.toDual ⊤, Finset.univ, ∅⟩

omit [Fintype M] [DecidableEq M] in
private theorem two_step_mass (rate : M → ℚ) (l r : M) (x : Unit × Unit) (y : Unit) :
    nativeWordEndpoint ((law rate).marked singletonParity) [l,r] x y = rate l * rate r := by
  simp [nativeWordEndpoint, law_marked]

private theorem wide_law_eq {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor}
    (a : WidenedState tests floor hf) :
    a.val.law = law a.val.law.rate := by
  apply PhysicalLaw.ext
  · rfl
  · funext p
    exact p.2.elim
  · funext m x y u v
    have h := a.val.legal.2.2.2.2.1.2.1 m x y u
    simpa [law] using h

private theorem profile_eq {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor}
    (a : WidenedState tests floor hf) :
    a.val.profile = wideProfile tests := by
  apply Capabilities.ext
  · have h := a.val.legal.2.2.2.2.2
    rw [wide_law_eq a] at h
    change registerMask (law a.val.law.rate).register = a.val.profile.mask.ofDual at h
    change a.val.profile.mask.ofDual = Set.univ
    rw [← h]
    ext e
    simp [registerMask, law]
  · funext j
    change (a.val.profile.grades j).ofDual = (⊤ : Setoid Unit)
    apply Setoid.ext
    intro x y
    cases x
    cases y
    exact iff_of_true ((a.val.profile.grades j).ofDual.iseqv.refl ()) ((⊤ : Setoid Unit).iseqv.refl ())
  · exact a.val.legal.2.1
  · exact Finset.eq_empty_of_forall_notMem (fun i => i.elim)

private theorem compiled_license (t : Test M) (rate : M → ℚ) (h : t.holds rate) :
    let p := EventExperiments.basePair (testPair t) (testSecond t)
    (⟨routeRateRow p.left p.right, 1⟩ : MonomialTest M).holds rate := by
  cases t
  · simpa [testSecond, testPair, EventExperiments.basePair, TimedPair.left, TimedPair.right, timed,
      route_rate_compile, Test.holds, wordMass] using h
  · simp [testSecond, testPair, EventExperiments.basePair, EventExperiments.reflexivePair,
      route_rate_compile, timed, TimedPair.left, TimedPair.right]

omit [Fintype M] [DecidableEq M] in
private theorem measurement_iff_holds (t : Test M) (rate : M → ℚ) (x : Unit × Unit) (y : Unit) :
    (let mass w := nativeWordEndpoint ((law rate).marked singletonParity) w x y
     mass (testPair t).left = mass (testPair t).right + (testSecond t).elim 0 (fun w => mass w.word)) ↔
    t.holds rate := by
  cases t <;> simp [testSecond, testPair, timed, TimedPair.left, TimedPair.right,
    wordList, two_step_mass, Test.holds, wordMass]

noncomputable def widenRate {tests : List (Test M)} {floor : ℚ} (hf : 0 < floor)
    (rate : {r : M → ℚ // Lawful tests floor r}) : WidenedState tests floor hf := by
  let p := wideProfile (M := M) tests
  refine ⟨⟨p, law rate.val, ?_⟩, ?_⟩
  · refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
    · intro _ _ _
      exact le_rfl
    · refine ⟨rate.2.2.1, rate.2.1, ?_⟩
      unfold Protocol.fiber ProbeCatalog.rateTests
      simp only [p, NativeExperiments.protocol, wideProfile, List.mem_append,
        List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]
      intro row hrow
      rcases hrow with ⟨i, hi⟩ | ⟨i, _⟩
      · rw [List.mem_singleton] at hi
        subst row
        exact compiled_license (tests.get i) rate.val (rate.2.2.2 _ (List.get_mem tests i))
      · exact i.elim
    · constructor
      · simp [p, Protocol.fiber, ProbeCatalog.spectralTests, NativeExperiments.protocol,
          wideProfile]
      · intro budget hbudget
        simp only [spectrumBudgets, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hbudget
        obtain ⟨mark, rfl⟩ := hbudget
        simp [law, EventExperiments.base, widened, NativeExperiments.protocol]
    · simp [RegisterValid, law, EventExperiments.base, widened, NativeExperiments.protocol, p,
        wideProfile, Protocol.fiber]
    · ext e
      simp [Protocol.fiber, p, wideProfile, registerMask, law]
  · intro i _ w hw x y
    have ht := rate.2.2.2 _ (List.get_mem tests i)
    have h := (measurement_iff_holds (tests.get i) rate.val x y).mpr ht
    change testSecond (tests.get i) = some w at hw
    simpa only [hw, Option.elim_some] using h

theorem wide_rate_lawful {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor}
    (a : WidenedState tests floor hf) : Lawful tests floor a.val.law.rate := by
  refine ⟨a.val.legal.2.2.1.2.1, a.val.legal.2.2.1.1, ?_⟩
  intro t ht
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  have hheld : i ∈ a.val.profile.licenses := by rw [profile_eq a]; exact Finset.mem_univ _
  have hj := (widened tests floor hf).licensed_joint_mass a hheld ((), ()) ()
  change (let mass w := nativeWordEndpoint (a.val.law.marked singletonParity) w ((), ()) ()
    mass (testPair (tests.get i)).left = mass (testPair (tests.get i)).right +
      (testSecond (tests.get i)).elim 0 (fun w => mass w.word)) at hj
  have hm := (measurement_iff_holds (tests.get i) a.val.law.rate ((), ()) ()).mp (by
    rw [wide_law_eq a] at hj
    exact hj)
  rwa [hi] at hm

noncomputable def fromFixed {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor}
    (a : EventState tests floor hf) : WidenedState tests floor hf :=
  widenRate hf ⟨a.val.law.rate, event_state_rate_lawful a⟩

private noncomputable def toFixed {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor}
    (a : WidenedState tests floor hf) : EventState tests floor hf :=
  liftEventState hf ⟨a.val.law.rate, wide_rate_lawful a⟩

private theorem toFixed_fromFixed {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor}
    (a : EventState tests floor hf) : toFixed (fromFixed a) = a :=
  lift_event_state_readback a

theorem fromFixed_injective {tests : List (Test M)} {floor : ℚ} {hf : 0 < floor} :
    Function.Injective (fromFixed (tests := tests) (floor := floor) (hf := hf)) :=
  Function.LeftInverse.injective toFixed_fromFixed

private theorem near_of_wide {tests : List (Test M)} {floor ε : ℚ} {hf : 0 < floor}
    {a b : WidenedState tests floor hf} :
    (widened tests floor hf).Step ε a b ↔ ∀ m, |a.val.law.rate m - b.val.law.rate m| < ε := by
  rw [(widened tests floor hf).step_iff_near_of_profile_eq ((profile_eq a).trans (profile_eq b).symm)]
  change PhysicalNear singletonParity ε a.val.law b.val.law ↔ _
  simp only [PhysicalNear]
  rw [wide_law_eq a, wide_law_eq b]
  simp only [law_marked]
  exact ⟨fun h m => h m ((), ()) ((), ()), fun h m _ _ => h m⟩

theorem widened_chain_iff {tests : List (Test M)} {floor ε : ℚ} {hf : 0 < floor}
    (a b : EventState tests floor hf) :
    (widened tests floor hf).Chain ε (fromFixed a) (fromFixed b) ↔
      Relation.ReflTransGen (NativeEventStep ε) a b := by
  constructor
  · intro h
    have hc := h.lift toFixed (fun p q hs => by
      apply (native_event_step_iff (a := toFixed p) (b := toFixed q) (ε := ε)).mpr
      exact ⟨wide_rate_lawful p, wide_rate_lawful q, near_of_wide.mp hs⟩)
    simpa only [toFixed_fromFixed] using hc
  · intro h
    exact h.lift fromFixed (fun p q hs => near_of_wide.mpr (native_event_step_iff.mp hs).2.2)

end MovingProjection.OneStateEvents
