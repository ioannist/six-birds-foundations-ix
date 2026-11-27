import MovingProjection.Experiments
import MovingProjection.Effects
import MovingProjection.Obstruction

/-! A coupled parity/register source on which all six effect tests are strict. -/

namespace MovingProjection.Example

open scoped BigOperators

abbrev Mark := Fin 4
abbrev Cell := Fin 4
abbrev Profile := Capabilities Mark Bool Cell Bool Bool 1

def parity : ParityBasis Unit Bool where
  value := fun _ x => if x then -1 else 1
  abs_eq_one := by intro _ x; cases x <;> norm_num
  balance := by intro i; simp
  orthogonal := by intro i j; cases i; cases j; norm_num [Fintype.sum_bool]

def testPair : Bool → TimedPair Mark 2
  | false => ⟨0,1,[0],[1],rfl,by decide⟩
  | true => ⟨2,3,[0],[0],rfl,by decide⟩

def check : Bool → AuditQuery Mark Unit 2
  | false => .calibration 1 () (1/4)
  | true => .calibration 2 () (1/8)

def experiment : NativeExperiments Mark Unit Bool Cell Bool Bool where
  parity := parity
  weights := fun _ => 1/4
  weights_pos := by intro _; norm_num
  weights_unit := by norm_num [Fin.sum_univ_succ]
  reversal := id
  reversal_involutive := fun _ => rfl
  δ := 1/8
  κ := 1/2
  δ_pos := by norm_num
  κ_lt_one := by norm_num
  horizon := 2
  license := testPair
  audit := check
  policy := fun _ => True

noncomputable abbrev D := experiment.protocol

abbrev State := D.State 1

def bit : Setoid Cell := Setoid.ker fun u : Cell => decide (u.val < 2)

def localGate (u v : Cell) : ℚ :=
  if u.val < 2 ∧ v.val < 2 then if u = v then 1/2 else 0 else 1/4

def table (gated : Bool) : Register Mark Bool Cell :=
  fun m x y u v =>
    if gated = true ∧ m = 2 ∧ x = false ∧ y = false then localGate u v else 1/4

private theorem table_nonneg (g : Bool) (m : Mark) (x y : Bool) (u v : Cell) :
    0 ≤ table g m x y u v := by
  unfold table
  split
  · unfold localGate
    split
    · split <;> norm_num
    · norm_num
  · norm_num

private theorem gate_rows (u : Cell) : ∑ v, localGate u v = 1 := by
  fin_cases u <;> norm_num [localGate, Fin.sum_univ_succ]

private theorem table_rows (g : Bool) (m : Mark) (x y : Bool) (u : Cell) :
    ∑ v, table g m x y u v = 1 := by
  by_cases h : g = true ∧ m = 2 ∧ x = false ∧ y = false
  · simp only [table, if_pos h, gate_rows]
  · norm_num [table, if_neg h, Fin.sum_univ_succ]

private theorem table_symmetric (g : Bool) (m : Mark) (x y : Bool) (u v : Cell) :
    table g m x y u v = table g m y x v u := by
  have h : (g = true ∧ m = 2 ∧ x = false ∧ y = false) ↔
      (g = true ∧ m = 2 ∧ y = false ∧ x = false) := by tauto
  simp only [table, h]
  by_cases hh : g = true ∧ m = 2 ∧ y = false ∧ x = false
  · simp only [localGate, and_comm, eq_comm]
  · simp [hh]

private theorem gate_blocks (u : Cell) (f : Cell → Bool)
    (h01 : f 0 = f 1) :
    (∑ v, if f v then localGate u v else 0) = ∑ v, if f v then (1/4 : ℚ) else 0 := by
  by_cases hf : f 0 = true <;>
    fin_cases u <;> norm_num [Fin.sum_univ_succ, localGate, ← h01, hf] <;> ring

private theorem valid_bit_table (g : Bool) :
    RegisterValid (fun _ : Cell => 1/4) (id : Mark → Mark) bit (table g) := by
  refine ⟨table_nonneg g, table_rows g, ?_, ?_, ?_⟩
  · intro m x y v
    simp_rw [table_symmetric g m x y]
    rw [← Finset.mul_sum, table_rows, mul_one]
  · intro m x y u v
    rw [table_symmetric g m x y u v]
    rfl
  · intro m x y u f hf
    have h01 : f 0 = f 1 := hf 0 1 (by rfl)
    by_cases h : g = true ∧ m = 2 ∧ x = false ∧ y = false
    · simp only [table, if_pos h]
      exact gate_blocks u f h01
    · simp only [table, if_neg h]

def packing (showBit : Bool) : Setoid Cell := if showBit then bit else ⊤

def grades (early terminal : Bool) (t : Fin 2) : (Setoid Cell)ᵒᵈ :=
  OrderDual.toDual (packing (if t = 0 then early else terminal))

def capabilities (gated earlier terminal licensed published : Bool) : Profile where
  mask := OrderDual.toDual (registerMask (table gated))
  grades := grades earlier terminal
  licenses := if licensed then {false,true} else {false}
  published := if published then {false,true} else {false}

def spectrum (a c : ℚ) (m : Mark × Unit) : ℚ :=
  match m.1.val with
  | 0 => a
  | 1 => 1/4
  | 2 => c
  | _ => 1/8

def law (g : Bool) (a c : ℚ) : PhysicalLaw Mark Unit Bool Cell :=
  ⟨fun _ => 1/4, spectrum a c, table g⟩

private theorem nested_grades {e t : Bool} (h : e = true → t = true) :
    Monotone (grades e t) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · cases e
    · change packing t ≤ (⊤ : Setoid Cell)
      exact le_top
    · have ht := h rfl
      subst t
      exact le_rfl
  · exact (show ¬ ((1 : Fin 2) ≤ 0) by decide) hij |>.elim
  · exact le_rfl

private theorem legal_example (g e t l p : Bool) (a c : ℚ)
    (hnested : e = true → t = true) (ha : a*a = (1/4 : ℚ)^2)
    (haBound : |a| ≤ 1/2) (hcBound : |c| ≤ 1/2)
    (hc : l = true ∨ p = true → c = 1/8) :
    D.legal (capabilities g e t l p) (law g a c) := by
  refine ⟨nested_grades hnested, True.intro, ⟨?_, ?_, ?_, rfl⟩⟩
  · refine ⟨fun _ => by norm_num [D, NativeExperiments.protocol, experiment, law], ?_, ?_⟩
    · norm_num [law, Fin.sum_univ_succ]
    · intro r hr
      change r ∈ D.checks.rateTests (capabilities g e t l p).licenses
        (capabilities g e t l p).published at hr
      simp only [ProbeCatalog.rateTests, List.mem_append, List.mem_flatMap] at hr
      rcases hr with ⟨b, _, hb⟩ | ⟨b, _, hb⟩
      · cases b <;> change r ∈ [⟨_,1⟩] at hb <;> obtain rfl := List.mem_singleton.mp hb <;>
          apply (route_rate_compile _ _ _ 1).2 <;>
          norm_num [experiment, testPair, TimedPair.left, TimedPair.right, law] <;> rfl
      · cases b <;> cases hb
  · refine ⟨?_, ?_⟩
    · intro r hr
      change r ∈ D.checks.spectralTests (capabilities g e t l p).licenses
        (capabilities g e t l p).published at hr
      simp only [ProbeCatalog.spectralTests,List.mem_append,List.mem_flatMap,Finset.mem_toList] at hr
      rcases hr with (hh | ⟨b,hb,hs⟩) | ⟨b,hb,hs⟩
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hh
        cases q
        simp [MonomialTest.holds, reversalTest, experiment]
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
        cases i
        cases b
        · change (routeCharacterTest [0,0] [1,1] ()).holds (fun mi => spectrum a c mi)
          let f (m : Mark) (i : Unit) := spectrum a c (m,i)
          change monomial (characterExponent [0,0] ()) (fun mi => f mi.1 mi.2) =
            1 * monomial (characterExponent [1,1] ()) (fun mi => f mi.1 mi.2)
          rw [character_monomial [0,0] () f, character_monomial [1,1] () f, one_mul]
          simpa [f, spectrum, pow_two] using ha
        · have hp : l = true := by cases l <;> simp_all [capabilities]
          change (routeCharacterTest [2,0] [3,0] ()).holds (fun mi => spectrum a c mi)
          let f (m : Mark) (i : Unit) := spectrum a c (m,i)
          change monomial (characterExponent [2,0] ()) (fun mi => f mi.1 mi.2) =
            1 * monomial (characterExponent [3,0] ()) (fun mi => f mi.1 mi.2)
          rw [character_monomial [2,0] () f, character_monomial [3,0] () f, one_mul]
          norm_num [f, spectrum, hc (Or.inl hp)]
      · cases b
        · change r ∈ [calibrationTest (1 : Mark) () (1/4)] at hs
          obtain rfl := List.mem_singleton.mp hs
          norm_num [MonomialTest.holds, calibrationTest, pointMonomial, spectrum, law, monomial,
            pointExponent, Fin.sum_univ_succ, Fintype.prod_prod_type]
        · have hp : p = true := by cases p <;> simp_all [capabilities]
          change r ∈ [calibrationTest (2 : Mark) () (1/8)] at hs
          obtain rfl := List.mem_singleton.mp hs
          have H : monomial (pointExponent ((2 : Mark), ())) (law g a c).spectrum =
              1/8 := by rw [pointMonomial]; norm_num [law, spectrum, hc (Or.inr hp)]
          simpa [MonomialTest.holds, calibrationTest, monomial] using H
    · intro b hb
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp hb
      change (∑ i : Unit, |spectrum a c (m,i)|) ≤ 1/2
      simp only [Fintype.sum_unique]
      fin_cases m <;> norm_num [spectrum] <;> assumption
  · apply (valid_bit_table g).coarsen
    cases t
    · exact le_top
    · exact le_rfl

noncomputable def initial : State :=
  ⟨capabilities false false false false false, law false (1/4) (-1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

noncomputable def gated : State :=
  ⟨capabilities true false false false false, law true (1/4) (-1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

noncomputable def throughZero : State :=
  ⟨capabilities true false false false false, law true (1/4) 0,
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

noncomputable def rewritten : State :=
  ⟨capabilities true false false false false, law true (1/4) (1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

noncomputable def packaged : State :=
  ⟨capabilities true false true false false, law true (1/4) (1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

noncomputable def disclosed : State :=
  ⟨capabilities true true true false false, law true (1/4) (1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

noncomputable def licensed : State :=
  ⟨capabilities true true true true false, law true (1/4) (1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (fun _ => rfl)⟩

noncomputable def published : State :=
  ⟨capabilities true true true true true, law true (1/4) (1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (fun _ => rfl)⟩

noncomputable def opposite : State :=
  ⟨capabilities false false false false false, law false (-1/4) (-1/8),
    legal_example _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)⟩

private def dampingWeight (mi : Mark × Unit) : ℕ := if mi.1 = 2 then 1 else 0

private theorem damping_on_unheld_mark (c : ℚ) (hc : c ≠ 0) :
    Damping ((D.fiber throughZero.profile).spectralChecks.map MonomialTest.row)
      (support (spectrum (1/4) c)) dampingWeight := by
  refine ⟨?_, ?_⟩
  · rintro ⟨m,i⟩ hm
    by_cases he : m = 2
    · subst m
      exact (hm (mem_support.mpr (show c ≠ 0 from hc))).elim
    · simp [dampingWeight, he]
  · intro r hr _
    obtain ⟨test, ht, rfl⟩ := List.mem_map.mp hr
    change test ∈ D.checks.spectralTests {false} {false} at ht
    simp only [ProbeCatalog.spectralTests, List.mem_append, List.mem_flatMap,
      Finset.mem_toList, Finset.mem_singleton, exists_eq_left] at ht
    rcases ht with (ht | ht) | ht
    · obtain ⟨⟨m,i⟩, _, rfl⟩ := List.mem_map.mp ht
      rfl
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
      cases i
      norm_num [D, NativeExperiments.protocol, experiment, TimedPair.left, TimedPair.right,
        testPair, routeCharacterTest, characterExponent, dampingWeight, Fintype.sum_prod_type,
        Fin.sum_univ_succ]
      decide
    · change test ∈ [calibrationTest (1 : Mark) () (1/4)] at ht
      obtain rfl := List.mem_singleton.mp ht
      norm_num [calibrationTest, pointExponent, dampingWeight, Fintype.sum_prod_type,
        Fin.sum_univ_succ]
      decide

private theorem signature_at_zero (c : ℚ) (hc : c ≠ 0) (hbound : |c| ≤ 1/2) :
    D.signature throughZero.profile throughZero.law =
      D.signature throughZero.profile (law true (1/4) c) := by
  have h := legal_example true false false false false (1/4) c
    (by decide) (by norm_num) (by norm_num) hbound (fun h => by cases h <;> contradiction)
  have hscale := fineConnected_scale h.2.2.2.1 (damping_on_unheld_mark c hc)
  have heq : scale (spectrum (1/4) c) dampingWeight 0 = throughZero.law.spectrum := by
    funext ⟨m,i⟩
    fin_cases m <;> simp [scale, dampingWeight, throughZero, law, spectrum]
  change FineConnected _ _ (scale (spectrum (1/4) c) dampingWeight 0) _ at hscale
  rw [heq] at hscale
  exact fineConnected_signedCore
    (bounded_of_budget_cover (spectrumBudgets_covers D.κ)) hscale

theorem gated_to_zero : D.Factorable gated throughZero := by
  exact (experiment.exact_six_iff _ _).2
    ⟨le_rfl, (signature_at_zero (-1/8) (by norm_num) (by norm_num)).symm⟩

theorem zero_to_rewritten : D.Factorable throughZero rewritten := by
  exact (experiment.exact_six_iff _ _).2
    ⟨le_rfl, signature_at_zero (1/8) (by norm_num) (by norm_num)⟩

theorem projected_law_changes :
    experiment.parity.kernel (fun i => gated.law.spectrum (2,i)) false false ≠
      experiment.parity.kernel (fun i => rewritten.law.spectrum (2,i)) false false := by
  norm_num [ParityBasis.kernel, experiment, parity, gated, rewritten, law, spectrum]

theorem register_depends_on_base :
    gated.law.register 2 false false 0 1 ≠ gated.law.register 2 true true 0 1 := by
  norm_num [gated, law, table, localGate]

theorem new_license_fails_before_rewrite :
    parity.nonemptyWord (fun m i => gated.law.spectrum (m,i)) 2 [0] ≠
      parity.nonemptyWord (fun m i => gated.law.spectrum (m,i)) 3 [0] := by
  intro h
  have hd := (parity.word_identity_iff (fun m i => gated.law.spectrum (m,i)) 2 3 [0] [0]).mp h ()
  norm_num [gated, law, spectrum] at hd

private def branch (s : State) : ℚ × ℚ :=
  (s.law.spectrum (0,()), s.law.spectrum (1,()))

private theorem branch_held (s : State) (h : initial.profile ≤ s.profile) :
    BinaryObstruction.held (branch s) := by
  have hup := Capabilities.le_coordinates.mp h
  have hroute : false ∈ s.profile.licenses := hup.2.2.1 (by decide)
  have haudit : false ∈ s.profile.published := hup.2.2.2 (by decide)
  have hl := (experiment.license_measured s hroute).2
  have hb := experiment.calibration_value s haudit (show experiment.audit false =
    .calibration (1 : Mark) () (1/4) from rfl)
  have hf := (parity.word_identity_iff (fun m i => s.law.spectrum (m,i))
    0 1 [0] [1]).mp hl ()
  have bound (m : Mark) : |s.law.spectrum (m,())| ≤ 1/2 := by
    have hh := spectrum_budget s.legal.2.2.2.1 m
    simpa only [Fintype.sum_unique] using hh
  refine ⟨bound 0, bound 1, hb, (BinaryObstruction.wordIdentity_iff _ _).mpr ?_⟩
  simpa only [branch, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hf

def obstructionTolerance : ℚ :=
  experiment.δ * (1/2) / (2*(Fintype.card (Bool × Cell) : ℚ)+1)

theorem obstructionTolerance_value : obstructionTolerance = 1/272 := by
  norm_num [obstructionTolerance, experiment, Fintype.card_prod, Fintype.card_fin]

theorem obstructionTolerance_pos : 0 < obstructionTolerance := by
  rw [obstructionTolerance_value]
  norm_num

theorem comparable_obstruction : initial.profile ≤ opposite.profile := le_rfl

theorem obstruction_at_native_tolerance : ¬ D.Chain obstructionTolerance initial opposite := by
  intro hc
  have agree (s : State) (h : D.Chain obstructionTolerance initial s) : branch initial = branch s := by
    induction h with
    | refl => rfl
    | @tail x y hp hs ih =>
      obtain ⟨e, he⟩ := hs
      have hprofile := Protocol.Chain.profile_le (show D.Chain obstructionTolerance initial x from hp)
      have ha := branch_held x hprofile
      have hb := branch_held y (hprofile.trans he.profile_le)
      by_cases hkind : e = .rewrite
      · subst e
        have hh : x.profile = y.profile ∧ PhysicalNear D.kernel obstructionTolerance x.law y.law := by
          simpa [Protocol.Step] using he
        have hphys : (D.fiber x.profile).step D.δ D.κ D.ν D.reverse D.kernel
            obstructionTolerance x.law y.law := ⟨x.legal.2.2, hh.1 ▸ y.legal.2.2, hh.2⟩
        have hd := spectralModulus_for_physicalStep D.kernel D.δ_pos D.κ_lt_one
          (show (0 : ℚ) < 1/2 by norm_num) hphys
        have H := hd.2.2 ((0 : Mark), ())
        have heq : branch x = branch y := by
          rcases BinaryObstruction.held_two_laws ha with hu | hu <;>
            rcases BinaryObstruction.held_two_laws hb with hv | hv
          · exact hu.trans hv.symm
          · change |(branch x).1 - (branch y).1| < 1/2 at H
            rw [hu,hv] at H
            norm_num [BinaryObstruction.positiveLaw, BinaryObstruction.negativeLaw] at H
          · change |(branch x).1 - (branch y).1| < 1/2 at H
            rw [hu,hv] at H
            norm_num [BinaryObstruction.positiveLaw, BinaryObstruction.negativeLaw] at H
          · exact hu.trans hv.symm
        exact ih.trans heq
      · exact ih.trans (congrArg (fun f : Mark × Unit → ℚ => (f (0,()), f (1,())))
          (he.spectrum_eq hkind))
  have hs := congrArg Prod.fst (agree opposite hc)
  norm_num [branch, initial, opposite, law, spectrum] at hs

theorem no_factorization : ¬ D.Factorable initial opposite := by
  intro h
  exact obstruction_at_native_tolerance (h obstructionTolerance obstructionTolerance_pos)

/-- Any presentation of the native experiments that preserves the allowed
small moves and both endpoint readouts inherits this obstruction. -/
theorem obstruction_under_equivalent_presentation {A : Type*} (decode : A → State)
    (moves : A → A → Prop)
    (preserves : ∀ u v, moves u v → ∃ e, D.Step obstructionTolerance e (decode u) (decode v))
    {u v : A} (hu : decode u = initial) (hv : decode v = opposite) :
    ¬ Relation.ReflTransGen moves u v := by
  intro h
  have hp : D.Chain obstructionTolerance (decode u) (decode v) := h.lift decode preserves
  rw [hu,hv] at hp
  exact obstruction_at_native_tolerance hp

/-- A change of native presentation cannot remove the obstruction. It is enough
to preserve measured trials and capability readouts under the translation. -/
theorem obstruction_preserved_by_readouts
    {A B : Type*} (realizeA : A → State) (realizeB : B → State) (translate : A ≃ B)
    (profile : ∀ a, (realizeA a).profile = (realizeB (translate a)).profile)
    (trials : ∀ a, (realizeA a).law.marked experiment.parity =
      (realizeB (translate a)).law.marked experiment.parity)
    {u v : A} (hu : realizeA u = initial) (hv : realizeA v = opposite) :
    ¬ D.Factorable (realizeB (translate u)) (realizeB (translate v)) := by
  intro h
  have h' := (experiment.factorization_preserved_by_readouts realizeA realizeB
    translate profile trials u v).mpr h
  rw [hu, hv] at h'
  exact no_factorization h'

end MovingProjection.Example
