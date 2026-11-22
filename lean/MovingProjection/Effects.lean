import MovingProjection.Capabilities

/-! The six semantic effects on observed law and capability profiles. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I]

inductive Effect
  | rewrite | gate | route | earlier | terminal | publication
  deriving DecidableEq, Repr

abbrev Protocol.Reached (D : Protocol M I X R Γ Δ) (n : ℕ) :=
  {p : Capabilities M X R Γ Δ n // ∃ a, D.legal p a}

@[ext] structure Protocol.State (D : Protocol M I X R Γ Δ) (n : ℕ) where
  profile : Capabilities M X R Γ Δ n
  law : PhysicalLaw M I X R
  legal : D.legal profile law

def Protocol.State.reached {D : Protocol M I X R Γ Δ} (x : D.State n) : D.Reached n :=
  ⟨x.profile, x.law, x.legal⟩

def Protocol.CapCover (D : Protocol M I X R Γ Δ)
    (p q : Capabilities M X R Γ Δ n) : Prop :=
  p < q ∧ ∀ r : Capabilities M X R Γ Δ n, (∃ a, D.legal r a) → p < r → ¬ r < q

def SingleGrade (p q : Capabilities M X R Γ Δ n) (t : Fin (n+1)) : Prop :=
  p.grades t ≠ q.grades t ∧ ∀ i, i ≠ t → p.grades i = q.grades i

def CapKind (e : Effect) (p q : Capabilities M X R Γ Δ n) : Prop :=
  match e with
  | .rewrite => False
  | .gate => p.mask ≠ q.mask ∧ p.grades = q.grades ∧
      p.licenses = q.licenses ∧ p.published = q.published
  | .route => p.mask = q.mask ∧ p.grades = q.grades ∧
      p.licenses ≠ q.licenses ∧ p.published = q.published
  | .earlier => p.mask = q.mask ∧ p.licenses = q.licenses ∧ p.published = q.published ∧
      ∃ t, t ≠ Fin.last n ∧ SingleGrade p q t
  | .terminal => p.mask = q.mask ∧ p.licenses = q.licenses ∧ p.published = q.published ∧
      SingleGrade p q (Fin.last n)
  | .publication => p.mask = q.mask ∧ p.grades = q.grades ∧
      p.licenses = q.licenses ∧ p.published ≠ q.published

def Protocol.Step (D : Protocol M I X R Γ Δ) (ε : ℚ) (e : Effect)
    (a b : D.State n) : Prop :=
  if e = .rewrite then a.profile = b.profile ∧ PhysicalNear D.kernel ε a.law b.law
  else D.CapCover a.profile b.profile ∧ CapKind e a.profile b.profile ∧
    if e = .gate then a.law.rate = b.law.rate ∧ a.law.spectrum = b.law.spectrum
    else a.law = b.law

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
theorem Protocol.Step.profile_le {D : Protocol M I X R Γ Δ} {ε : ℚ} {e : Effect}
    {a b : D.State n} (h : D.Step ε e a b) : a.profile ≤ b.profile := by
  unfold Step at h
  split at h
  · exact h.1.le
  · exact h.1.1.le

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
theorem Protocol.Step.spectrum_eq {D : Protocol M I X R Γ Δ} {ε : ℚ} {e : Effect}
    {a b : D.State n} (h : D.Step ε e a b) (hne : e ≠ .rewrite) :
    a.law.spectrum = b.law.spectrum := by
  simp only [Step, if_neg hne] at h
  by_cases hh : e = .gate
  · exact (if_pos hh ▸ h.2.2).2
  · have hLaw : a.law = b.law := by simpa only [if_neg hh] using h.2.2
    exact congrArg PhysicalLaw.spectrum hLaw

private theorem cover_eq_right {A : Type*} [PartialOrder A] {a b z : A}
    (hab : a ⋖ b) (haz : a < z) (hzb : z ≤ b) : z = b :=
  hzb.eq_of_not_lt (hab.2 haz)

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
theorem Protocol.cover_reached_iff {D : Protocol M I X R Γ Δ} {p q : D.Reached n} :
    p ⋖ q ↔ D.CapCover p.1 q.1 := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro r hr hpr hrq
    exact h.2 (show p < (⟨r,hr⟩ : D.Reached n) from hpr)
      (show (⟨r,hr⟩ : D.Reached n) < q from hrq)
  · intro h
    exact ⟨h.1, fun r hpr hrq => h.2 r.1 r.2 hpr hrq⟩

omit [DecidableEq M] in
theorem Protocol.reached_chain {D : Protocol M I X R Γ Δ} {p q : D.Reached n} (h : p ≤ q) :
    Relation.ReflTransGen (fun a b : D.Reached n => a ⋖ b) p q := by
  classical
  letI : LocallyFiniteOrder (D.Reached n) :=
    LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _
  exact le_iff_reflTransGen_covBy.mp h

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
/-- The ordinary capability order lets the new support be held alongside the
earlier graded, route and publication tests. The witness physically changes
the conditional register while retaining the earlier rate and projected law. -/
theorem Protocol.mask_mixture (D : Protocol M I X R Γ Δ) {p q : Capabilities M X R Γ Δ n}
    (hpq : p ≤ q) {a c : PhysicalLaw M I X R} (ha : D.legal p a) (hc : D.legal q c) :
    D.legal {p with mask := q.mask} ⟨a.rate, a.spectrum, c.register⟩ := by
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ?_, ?_⟩
  · exact hc.2.2.2.2.1.coarsen ((Capabilities.le_coordinates.mp hpq).2.1 _)
  · change registerMask c.register = q.mask.ofDual
    exact Protocol.legal_mask hc

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
set_option maxHeartbeats 500000 in
theorem Protocol.capKind_of_cover (D : Protocol M I X R Γ Δ)
    {u v : D.Reached n} (h : u ⋖ v) : ∃ e, e ≠ .rewrite ∧ CapKind e u.1 v.1 := by
  classical
  obtain ⟨a, ha⟩ := u.2
  obtain ⟨b, hb⟩ := v.2
  let p := u.1
  let q := v.1
  change D.legal p a at ha
  change D.legal q b at hb
  change ∃ e, e ≠ .rewrite ∧ CapKind e p q
  have hpq : p ≤ q := h.1.le
  obtain ⟨hm, hg, hl, he⟩ := Capabilities.le_coordinates.mp hpq
  have noMiddle (z : Capabilities M X R Γ Δ n) (hz : ∃ l, D.legal z l)
      (hpz : p ≤ z) (hzq : z ≤ q) (hne : p ≠ z) : z = q := by
    let w : D.Reached n := ⟨z,hz⟩
    have H : u < w := lt_of_le_of_ne hpz (fun hh => hne (congrArg Subtype.val hh))
    exact congrArg Subtype.val (cover_eq_right h H hzq)
  by_cases hmask : p.mask = q.mask
  · have hMb : registerMask b.register = p.mask.ofDual :=
      (Protocol.legal_mask hb).trans (congrArg OrderDual.ofDual hmask.symm)
    by_cases hlicense : p.licenses = q.licenses
    · by_cases hreceipt : p.published = q.published
      · have hd : p.grades ≠ q.grades := by
          intro hh
          exact h.1.ne (Subtype.ext (Capabilities.ext hmask hh hlicense hreceipt))
        let U := Finset.univ.filter fun j : Fin (n+1) => p.grades j ≠ q.grades j
        have hex : U.Nonempty := by
          by_contra H
          apply hd
          funext j
          by_contra hj
          exact H ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
        let t := U.max' hex
        have ht : p.grades t ≠ q.grades t := (Finset.mem_filter.mp
          (Finset.max'_mem U hex)).2
        have hlater (j : Fin (n+1)) (htj : t < j) : p.grades j = q.grades j := by
          by_contra hh
          exact htj.not_ge (Finset.le_max' U j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩))
        let z : Capabilities M X R Γ Δ n := {p with grades := Function.update p.grades t (q.grades t)}
        have ht' : z.grades t = q.grades t := Function.update_self _ _ _
        have hi' (i : Fin (n+1)) (hi : i ≠ t) : z.grades i = p.grades i :=
          Function.update_of_ne hi _ _
        have hnest : z.nested := by
          intro i j hij
          by_cases hi : i = t
          · subst i
            rw [ht']
            by_cases hj : j = t
            · subst j
              rw [ht']
            · rw [hi' j hj, hlater j (lt_of_le_of_ne hij (Ne.symm hj))]
              exact hb.1 hij
          · rw [hi' i hi]
            by_cases hj : j = t
            · subst j
              rw [ht']
              exact (ha.1 hij).trans (hg t)
            · rw [hi' j hj]
              exact ha.1 hij
        have hpz : p ≤ z := by
          refine Capabilities.le_coordinates.mpr ⟨fun _ H => H, ?_, fun _ H => H, fun _ H => H⟩
          intro i
          by_cases hi : i = t
          · subst i
            rw [ht']
            exact hg t
          · rw [hi' i hi]
        have hzq : z ≤ q := by
          refine Capabilities.le_coordinates.mpr ⟨hm, ?_, hl, he⟩
          intro i
          by_cases hi : i = t
          · subst i
            rw [ht']
          · rw [hi' i hi]
            exact hg i
        have hz : D.legal z b := ⟨hnest, ha.2.1, (D.legal_to_earlier hzq hb).mpr hMb⟩
        have hqz : z = q := noMiddle z ⟨b,hz⟩ hpz hzq (fun H =>
          ht ((congrArg (fun c : Capabilities M X R Γ Δ n => c.grades t) H).trans ht'))
        have hsingle : SingleGrade p q t := by
          refine ⟨ht, fun i hi => ?_⟩
          exact (hi' i hi).symm.trans (congrArg (fun c : Capabilities M X R Γ Δ n => c.grades i) hqz)
        by_cases htlast : t = Fin.last n
        · exact ⟨.terminal, by decide, hmask, hlicense, hreceipt, htlast ▸ hsingle⟩
        · exact ⟨.earlier, by decide, hmask, hlicense, hreceipt, t, htlast, hsingle⟩
      · let z : Capabilities M X R Γ Δ n := {p with published := q.published}
        have hpz : p ≤ z := Capabilities.le_coordinates.mpr
          ⟨fun _ H => H, fun _ => le_rfl, fun _ H => H, he⟩
        have hzq : z ≤ q := Capabilities.le_coordinates.mpr ⟨hm, hg, hl, fun _ H => H⟩
        have hz : D.legal z b := ⟨ha.1, ha.2.1, (D.legal_to_earlier hzq hb).mpr hMb⟩
        have H := noMiddle z ⟨b,hz⟩ hpz hzq (fun h => by
          have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.published) h
          exact hreceipt hEq)
        have hgs : p.grades = q.grades := by
          have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.grades) H
          exact hEq
        exact ⟨.publication, by decide, hmask, hgs, hlicense, hreceipt⟩
    · let z : Capabilities M X R Γ Δ n := {p with licenses := q.licenses}
      have hpz : p ≤ z := Capabilities.le_coordinates.mpr
        ⟨fun _ H => H, fun _ => le_rfl, hl, fun _ H => H⟩
      have hzq : z ≤ q := Capabilities.le_coordinates.mpr ⟨hm, hg, fun _ H => H, he⟩
      have hz : D.legal z b := ⟨ha.1, hb.2.1, (D.legal_to_earlier hzq hb).mpr hMb⟩
      have H := noMiddle z ⟨b,hz⟩ hpz hzq (fun h => by
        have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.licenses) h
        exact hlicense hEq)
      have hgs : p.grades = q.grades := by
        have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.grades) H
        exact hEq
      have hes : p.published = q.published := by
        have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.published) H
        exact hEq
      exact ⟨.route, by decide, hmask, hgs, hlicense, hes⟩
  · let z : Capabilities M X R Γ Δ n := {p with mask := q.mask}
    have hpz : p ≤ z := Capabilities.le_coordinates.mpr
      ⟨hm, fun _ => le_rfl, fun _ H => H, fun _ H => H⟩
    have hzq : z ≤ q := Capabilities.le_coordinates.mpr ⟨fun _ H => H, hg, hl, he⟩
    have hz := D.mask_mixture hpq ha hb
    have H := noMiddle z ⟨_,hz⟩ hpz hzq (fun h => by
      have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.mask) h
      exact hmask hEq)
    have hgs : p.grades = q.grades := by
      have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.grades) H
      exact hEq
    have hls : p.licenses = q.licenses := by
      have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.licenses) H
      exact hEq
    have hes : p.published = q.published := by
      have hEq := congrArg (fun c : Capabilities M X R Γ Δ n => c.published) H
      exact hEq
    exact ⟨.gate, by decide, hmask, hgs, hls, hes⟩

end MovingProjection
