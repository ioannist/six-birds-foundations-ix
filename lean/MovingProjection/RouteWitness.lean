import MovingProjection.WitnessInput
import MovingProjection.NativeWords

/-! The actual route edit supplies parallel paths and a finite monoid
certificate against the entire source rule list. -/

namespace MovingProjection.Example

structure RouteSummary where
  elapsed : ℕ
  probability : ℚ
  response : ℚ
  deriving DecidableEq

def finiteRouteWords : Finset (List Mark) :=
  ({[]} : Finset _) ∪ (Finset.univ : Finset Mark).image (fun m => [m]) ∪
    (Finset.univ : Finset (Mark × Mark)).image (fun p => [p.1,p.2])

theorem finiteRouteWords_iff (w : List Mark) : w ∈ finiteRouteWords ↔ w.length ≤ 2 := by
  cases w with
  | nil => simp [finiteRouteWords]
  | cons m w =>
    cases w with
    | nil => simp [finiteRouteWords]
    | cons k w =>
      cases w with
      | nil => simp [finiteRouteWords]
      | cons j w => simp [finiteRouteWords]

def timedRoute (s : State) (w : List Mark) : Option RouteSummary :=
  if w.length ≤ 2 then some ⟨w.length,(w.map s.law.rate).prod,
    (w.map (fun m => s.law.spectrum (m,()))).prod⟩ else none

def routeStates (s : State) : Finset (Option RouteSummary) :=
  insert none (finiteRouteWords.image (timedRoute s))

theorem timedRoute_mem (s : State) (w : List Mark) : timedRoute s w ∈ routeStates s := by
  unfold routeStates
  by_cases h : w.length ≤ 2
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w,(finiteRouteWords_iff w).mpr h,rfl⟩)
  · rw [timedRoute, if_neg h]
    exact Finset.mem_insert_self _ _

def advanceRoute (s : State) (m : Mark) : Option RouteSummary → Option RouteSummary
  | none => none
  | some p =>
      if p.elapsed < 2 then some ⟨p.elapsed + 1,p.probability * s.law.rate m,
        p.response * s.law.spectrum (m,())⟩ else none

theorem advanceRoute_append (s : State) (m : Mark) (w : List Mark) :
    advanceRoute s m (timedRoute s w) = timedRoute s (w ++ [m]) := by
  by_cases hw : w.length ≤ 2
  · by_cases h : w.length < 2
    · have h' : (w ++ [m]).length ≤ 2 := by simpa using Nat.succ_le_of_lt h
      rw [timedRoute, if_pos hw, timedRoute, if_pos h']
      simp [h, advanceRoute]
    · have h' : ¬ (w ++ [m]).length ≤ 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        omega
      rw [timedRoute, if_pos hw, timedRoute, if_neg h']
      simp [h, advanceRoute]
  · have h' : ¬ (w ++ [m]).length ≤ 2 := by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      omega
    rw [timedRoute, if_neg hw, timedRoute, if_neg h']
    rfl

def routeMove (s : State) (m : Mark) : (routeStates s) → (routeStates s) :=
  fun p => ⟨advanceRoute s m p.val, by
    have h := p.property
    unfold routeStates at h
    rcases Finset.mem_insert.mp h with hn | hi
    · rw [hn]
      exact Finset.mem_insert_self _ _
    · obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hi
      rw [← hw, advanceRoute_append]
      exact timedRoute_mem s _⟩

def reachedBy (s : State) (w : List Mark) : routeStates s :=
  ⟨timedRoute s w,timedRoute_mem s w⟩

theorem routeMove_reachedBy (s : State) (m : Mark) (w : List Mark) :
    routeMove s m (reachedBy s w) = reachedBy s (w ++ [m]) :=
  Subtype.ext (advanceRoute_append s m w)

theorem newly_licensed_routes_parallel :
    routeMove disclosed 0 (routeMove disclosed 2 (reachedBy disclosed [])) =
      routeMove disclosed 0 (routeMove disclosed 3 (reachedBy disclosed [])) := by
  rw [routeMove_reachedBy, routeMove_reachedBy, routeMove_reachedBy, routeMove_reachedBy]
  apply Subtype.ext
  norm_num [reachedBy, timedRoute, disclosed, law, spectrum]

theorem newly_licensed_route_endpoints_were_distinct :
    reachedBy gated [2,0] ≠ reachedBy gated [3,0] := by
  intro h
  have hh := congrArg Subtype.val h
  norm_num [reachedBy, timedRoute, gated, law, spectrum] at hh

/-- The entire rule list is the one selected from the source's licenses. -/
noncomputable def sourceRules : List (List Mark × List Mark) :=
  disclosed.profile.licenses.toList.map fun g => ((testPair g).left,(testPair g).right)

def routeSeparator (w : List Mark) : Bool := w.any (fun m => m == 2)

theorem routeSeparator_mul (u v : List Mark) :
    routeSeparator (u ++ v) = (routeSeparator u || routeSeparator v) := by
  simp [routeSeparator, List.any_append]

theorem routeSeparator_monoid_laws :
    (∀ x : Bool, (false || x) = x ∧ (x || false) = x) ∧
      (∀ x y z : Bool, ((x || y) || z) = (x || (y || z))) := by
  decide

theorem routeSeparator_checks_all_rules :
    ∀ rule ∈ sourceRules, routeSeparator rule.1 = routeSeparator rule.2 := by
  intro rule hr
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hr
  have h : g ∈ ({false} : Finset Bool) := Finset.mem_toList.mp hg
  rcases Finset.mem_singleton.mp h with rfl
  decide

theorem routeSeparator_distinguishes :
    routeSeparator (testPair true).left ≠ routeSeparator (testPair true).right := by
  decide

def SourceRewrite (w z : List Mark) : Prop :=
  ∃ pre post rule, rule ∈ sourceRules ∧
    ((w = pre ++ rule.1 ++ post ∧ z = pre ++ rule.2 ++ post) ∨
      (w = pre ++ rule.2 ++ post ∧ z = pre ++ rule.1 ++ post))

theorem sourceRewrite_preserves_separator {w z : List Mark} (h : SourceRewrite w z) :
    routeSeparator w = routeSeparator z := by
  obtain ⟨pre,post,rule,hr,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ := h
  · simp only [routeSeparator_mul,routeSeparator_checks_all_rules _ hr]
  · simp only [routeSeparator_mul,routeSeparator_checks_all_rules _ hr]

theorem held_rules_do_not_identify_new_routes :
    ¬ Relation.ReflTransGen SourceRewrite (testPair true).left (testPair true).right := by
  intro h
  have invariant {u v} (path : Relation.ReflTransGen SourceRewrite u v) :
      routeSeparator u = routeSeparator v := by
    induction path with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (sourceRewrite_preserves_separator hstep)
  exact routeSeparator_distinguishes (invariant h)

end MovingProjection.Example
