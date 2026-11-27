import MovingProjection.NativeWords

/-! An extension of audited Markov experiments that changes only the
syntax of route licenses. A license can compare a word with a two-word
event. Attained profiles are formed using the widened legality predicate. -/

namespace MovingProjection

open scoped BigOperators

structure SecondWord {M : Type*} {H : ℕ} (pair : TimedPair M H) where
  word : List M
  duration : word.length = pair.left.length
  distinct : word ≠ pair.right

theorem SecondWord.fits {M : Type*} {H : ℕ} {pair : TimedPair M H}
    (w : SecondWord pair) : w.word.length ≤ H := by
  rw [w.duration]
  exact pair.fits

variable {M I X R Γ Δ : Type*}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [DecidableEq X]

omit [Fintype Γ] [Fintype Δ] in
/-- For a positive lawful native law, measured joint equality of singleton
words is the original equality of masses and conditional projected laws. -/
theorem NativeExperiments.singleton_joint_iff [Nonempty X] [Nonempty R]
    (D : NativeExperiments M I X R Γ Δ) {n : ℕ} (s : D.protocol.State n)
    (u v : List M) :
    (∀ x y, nativeWordEndpoint (s.law.marked D.parity) u x y =
      nativeWordEndpoint (s.law.marked D.parity) v x y) ↔
    (u.map s.law.rate).prod = (v.map s.law.rate).prod ∧
      projectedWordEndpoint (fun m => D.parity.kernel (fun i => s.law.spectrum (m,i))) u =
        projectedWordEndpoint (fun m => D.parity.kernel (fun i => s.law.spectrum (m,i))) v := by
  let α (m : M) (i : I) := s.law.spectrum (m,i)
  have hf (w : List M) (x : X × R) (y : X) :
      nativeWordEndpoint (s.law.marked D.parity) w x y = (w.map s.law.rate).prod *
        projectedWordEndpoint (fun m => D.parity.kernel (α m)) w x.1 y :=
    nativeWordEndpoint_factor D.parity α _ _ s.legal.2.2.2.2.1.2.1 w x y
  constructor
  · intro h
    let s₀ : X × R := Classical.choice inferInstance
    have he : (u.map s.law.rate).prod = (v.map s.law.rate).prod := by
      rw [← D.native_word_mass s u s₀, ← D.native_word_mass s v s₀]
      exact Finset.sum_congr rfl (fun y _ => h s₀ y)
    refine ⟨he, ?_⟩
    funext x y
    let r₀ : R := Classical.choice inferInstance
    have e := h (x,r₀) y
    rw [hf, hf, he] at e
    have hp : 0 < (v.map s.law.rate).prod := by
      apply List.prod_pos
      intro rate hr
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hr
      exact D.δ_pos.trans_le (s.legal.2.2.1.1 m)
    exact mul_left_cancel₀ hp.ne' e
  · rintro ⟨hm, hq⟩ x y
    rw [hf, hf, hm]
    exact congrArg (fun f : X → X → ℚ => (v.map s.law.rate).prod * f x.1 y) hq

structure EventExperiments (M I X R Γ Δ : Type*) [Fintype X] [Fintype R] [DecidableEq I] where
  native : NativeExperiments M I X R Γ Δ
  second : (g : Γ) → Option (SecondWord (native.license g))

namespace EventExperiments

variable (E : EventExperiments M I X R Γ Δ) {n : ℕ}

def reflexivePair {H : ℕ} (p : TimedPair M H) : TimedPair M H :=
  ⟨p.first, p.first, p.tail, p.tail, rfl, p.fits⟩

def basePair {H : ℕ} (p : TimedPair M H) (extra : Option (SecondWord p)) : TimedPair M H :=
  if extra.isSome then reflexivePair p else p

/-- For a widened license the singleton compilation uses a reflexive pair.
The actual numerical test is imposed by `holds`. -/
def base : NativeExperiments M I X R Γ Δ :=
  { E.native with license := fun g => basePair (E.native.license g) (E.second g) }

omit [Fintype M] [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq X] in
theorem base_license_eq (g : Γ) (h : E.second g = none) :
    E.base.license g = E.native.license g := by simp [base, basePair, h]

omit [Fintype M] [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq X] in
theorem base_license_reflexive (g : Γ) {w : SecondWord (E.native.license g)}
    (h : E.second g = some w) :
    (E.base.license g).left = (E.base.license g).right := by
  simp [base, basePair, h, reflexivePair, TimedPair.left, TimedPair.right]

def holds (p : Capabilities M X R Γ Δ n) (a : PhysicalLaw M I X R) : Prop :=
  ∀ g ∈ p.licenses, ∀ w, E.second g = some w → ∀ x y,
    nativeWordEndpoint (a.marked E.native.parity) (E.native.license g).left x y =
      nativeWordEndpoint (a.marked E.native.parity) (E.native.license g).right x y +
        nativeWordEndpoint (a.marked E.native.parity) w.word x y

abbrev State (n : ℕ) := {a : E.base.protocol.State n // E.holds a.profile a.law}

omit [Fintype Γ] [Fintype Δ] in
theorem licensed_joint_mass [Nonempty X] (a : E.State n) {g : Γ}
    (hg : g ∈ a.val.profile.licenses) (x : X × R) (y : X) :
    let mass w := nativeWordEndpoint (a.val.law.marked E.native.parity) w x y
    mass (E.native.license g).left =
      mass (E.native.license g).right + (E.second g).elim 0 (fun w => mass w.word) := by
  cases h : E.second g with
  | none =>
    have hs := E.base.licensed_trajectory_test a.val hg x y
    rw [E.base_license_eq g h] at hs
    simpa only [h, Option.elim_none, add_zero] using hs
  | some w =>
    simpa only [h, Option.elim_some] using a.property g hg w h x y

def Cover (p q : Capabilities M X R Γ Δ n) : Prop :=
  p < q ∧ ∀ r : Capabilities M X R Γ Δ n,
    (∃ a, E.base.protocol.legal r a ∧ E.holds r a) → p < r → ¬ r < q

/-- The unlabelled numerical and cover edits of the audited instrument.
Equality of laws and of rate/spectrum pairs express the corresponding
equalities of the full and projected prepared tables. -/
def Step (ε : ℚ) (a b : E.State n) : Prop :=
  (a.val.profile = b.val.profile ∧ PhysicalNear E.native.parity ε a.val.law b.val.law) ∨
    (E.Cover a.val.profile b.val.profile ∧
      ((a.val.profile.mask = b.val.profile.mask ∧ a.val.law = b.val.law) ∨
        (a.val.profile.mask ≠ b.val.profile.mask ∧
          a.val.law.rate = b.val.law.rate ∧ a.val.law.spectrum = b.val.law.spectrum)))

abbrev Chain (ε : ℚ) := Relation.ReflTransGen (E.Step (n := n) ε)

def Factorable (a b : E.State n) : Prop := ∀ ε : ℚ, 0 < ε → E.Chain ε a b

omit [Fintype Γ] [Fintype Δ] in
theorem Step.profile_le {E : EventExperiments M I X R Γ Δ} {ε : ℚ} {a b : E.State n}
    (h : E.Step ε a b) : a.val.profile ≤ b.val.profile :=
  h.elim (fun hr => hr.1.le) (fun hc => hc.1.1.le)

omit [Fintype Γ] [Fintype Δ] in
theorem Chain.profile_le {E : EventExperiments M I X R Γ Δ} {ε : ℚ} {a b : E.State n}
    (h : E.Chain ε a b) : a.val.profile ≤ b.val.profile := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans hstep.profile_le

omit [Fintype Γ] [Fintype Δ] in
theorem step_iff_near_of_profile_eq {ε : ℚ} {a b : E.State n}
    (hp : a.val.profile = b.val.profile) :
    E.Step ε a b ↔ PhysicalNear E.native.parity ε a.val.law b.val.law := by
  constructor
  · exact fun h => h.elim And.right (fun hc => (hc.1.1.ne hp).elim)
  · exact fun h => Or.inl ⟨hp, h⟩

def ofNative (D : NativeExperiments M I X R Γ Δ) : EventExperiments M I X R Γ Δ :=
  ⟨D, fun _ => none⟩

omit [Fintype M] [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq X] in
@[simp] theorem base_ofNative (D : NativeExperiments M I X R Γ Δ) :
    (ofNative D).base = D := rfl

def liftNative (D : NativeExperiments M I X R Γ Δ) (a : D.protocol.State n) :
    (ofNative D).State n :=
  ⟨a, fun _ _ _ h => by cases h⟩

omit [Fintype Γ] [Fintype Δ] in
theorem cover_ofNative_iff (D : NativeExperiments M I X R Γ Δ)
    (p q : Capabilities M X R Γ Δ n) :
    (ofNative D).Cover p q ↔ D.protocol.CapCover p q := by
  have hv (r : Capabilities M X R Γ Δ n) (a : PhysicalLaw M I X R) :
      (ofNative D).holds r a := fun _ _ _ h => by cases h
  simp [Cover, Protocol.CapCover, hv]

omit [Fintype Γ] [Fintype Δ] in
theorem step_ofNative_iff (D : NativeExperiments M I X R Γ Δ) (a b : D.protocol.State n)
    (ε : ℚ) :
    (ofNative D).Step ε (liftNative D a) (liftNative D b) ↔
      ∃ e, D.protocol.Step ε e a b := by
  change ((a.profile = b.profile ∧ PhysicalNear D.parity ε a.law b.law) ∨
    ((ofNative D).Cover a.profile b.profile ∧
      ((a.profile.mask = b.profile.mask ∧ a.law = b.law) ∨
        (a.profile.mask ≠ b.profile.mask ∧
          a.law.rate = b.law.rate ∧ a.law.spectrum = b.law.spectrum)))) ↔ _
  rw [cover_ofNative_iff]
  constructor
  · rintro (h | ⟨hc, h⟩)
    · exact ⟨.rewrite, by simpa [Protocol.Step, NativeExperiments.protocol] using h⟩
    · obtain ⟨e, he, hk⟩ :=
        D.protocol.capKind_of_cover (D.protocol.cover_reached_iff.mpr hc :
          a.reached ⋖ b.reached)
      refine ⟨e, ?_⟩
      simp only [Protocol.Step, if_neg he]
      change CapKind e a.profile b.profile at hk
      refine ⟨hc, hk, ?_⟩
      rcases h with (⟨hm, h⟩ | ⟨hm, h⟩) <;> cases e <;> simp_all [CapKind]
  · rintro ⟨e, he⟩
    by_cases hr : e = .rewrite
    · subst e
      exact Or.inl (by simpa [Protocol.Step, NativeExperiments.protocol] using he)
    · simp only [Protocol.Step, if_neg hr] at he
      rcases he with ⟨hc, hk, he⟩
      exact Or.inr ⟨hc, by cases e <;> simp_all [CapKind]⟩

omit [Fintype Γ] [Fintype Δ] in
private theorem lift_native_val (D : NativeExperiments M I X R Γ Δ)
    (a : (ofNative D).State n) : liftNative D a.val = a := Subtype.ext rfl

omit [Fintype Γ] [Fintype Δ] in
theorem chain_ofNative_iff (D : NativeExperiments M I X R Γ Δ) (a b : D.protocol.State n)
    (ε : ℚ) :
    (ofNative D).Chain ε (liftNative D a) (liftNative D b) ↔ D.protocol.Chain ε a b := by
  constructor
  · intro h
    exact h.lift (p := fun u v => ∃ e, D.protocol.Step ε e u v)
      (fun u => u.val) (fun u v (hstep : (ofNative D).Step ε u v) =>
      show ∃ e, D.protocol.Step ε e u.val v.val from
        (step_ofNative_iff D u.val v.val ε).mp (by
        rw [lift_native_val, lift_native_val]
        exact hstep))
  · intro h
    exact h.lift (liftNative D) (fun u v hstep => (step_ofNative_iff D u v ε).mpr hstep)

omit [Fintype Γ] [Fintype Δ] in
theorem factorable_ofNative_iff (D : NativeExperiments M I X R Γ Δ) (a b : D.protocol.State n) :
    (ofNative D).Factorable (liftNative D a) (liftNative D b) ↔ D.protocol.Factorable a b :=
  forall_congr' fun ε => imp_congr_right fun _ => chain_ofNative_iff D a b ε

end EventExperiments

end MovingProjection
