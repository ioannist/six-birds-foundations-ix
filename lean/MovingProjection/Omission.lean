import MovingProjection.Effects

/-! Omission invariants of the measured effects, independent of the choice of
support gate or the number of rewrites. -/

namespace MovingProjection

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq I]

abbrev Protocol.Omitting (D : Protocol M I X R Γ Δ) (e : Effect) (ε : ℚ) :=
  Relation.ReflTransGen (fun a b : D.State n => ∃ k ≠ e, D.Step ε k a b)

private theorem chain_invariant {A B : Type*} {rel : A → A → Prop} {x y : A}
    (h : Relation.ReflTransGen rel x y) (f : A → B)
    (hs : ∀ {u v}, rel u v → f u = f v) : f x = f y := by
  induction h with
  | refl => rfl
  | tail _ hh ih => exact ih.trans (hs hh)

private theorem mask_step {D : Protocol M I X R Γ Δ} {ε : ℚ} {k : Effect}
    {a b : D.State n} (h : D.Step ε k a b) (hne : k ≠ .gate) :
    a.profile.mask = b.profile.mask := by
  cases k <;> simp_all [Protocol.Step, CapKind]

private theorem route_step {D : Protocol M I X R Γ Δ} {ε : ℚ} {k : Effect}
    {a b : D.State n} (h : D.Step ε k a b) (hne : k ≠ .route) :
    a.profile.licenses = b.profile.licenses := by
  cases k <;> simp_all [Protocol.Step, CapKind]

private theorem publication_step {D : Protocol M I X R Γ Δ} {ε : ℚ} {k : Effect}
    {a b : D.State n} (h : D.Step ε k a b) (hne : k ≠ .publication) :
    a.profile.published = b.profile.published := by
  cases k <;> simp_all [Protocol.Step, CapKind]

private theorem terminal_step {D : Protocol M I X R Γ Δ} {ε : ℚ} {k : Effect}
    {a b : D.State n} (h : D.Step ε k a b) (hne : k ≠ .terminal) :
    a.profile.grades (Fin.last n) = b.profile.grades (Fin.last n) := by
  cases k <;> simp_all [Protocol.Step, CapKind, SingleGrade]
  obtain ⟨i, hi, _, hh⟩ := h.2.1.2.2.2
  exact hh _ (Ne.symm hi)

private theorem earlier_step {D : Protocol M I X R Γ Δ} {ε : ℚ} {k : Effect}
    {a b : D.State n} (h : D.Step ε k a b) (hne : k ≠ .earlier)
    {i : Fin (n+1)} (hi : i ≠ Fin.last n) :
    a.profile.grades i = b.profile.grades i := by
  cases k <;> simp_all [Protocol.Step, CapKind, SingleGrade]

theorem Protocol.Omitting.support {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .gate ε a b) :
    a.profile.mask = b.profile.mask :=
  chain_invariant h (fun s => s.profile.mask) (by rintro _ _ ⟨_, hne, hstep⟩; exact mask_step hstep hne)

theorem Protocol.Omitting.licenses {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .route ε a b) :
    a.profile.licenses = b.profile.licenses :=
  chain_invariant h (fun s => s.profile.licenses) (by rintro _ _ ⟨_, hn, hs⟩; exact route_step hs hn)

theorem Protocol.Omitting.citations {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .publication ε a b) :
    a.profile.published = b.profile.published :=
  chain_invariant h (fun s => s.profile.published) (by rintro _ _ ⟨_, hn, hs⟩; exact publication_step hs hn)

theorem Protocol.Omitting.terminal {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .terminal ε a b) :
    a.profile.grades (Fin.last n) = b.profile.grades (Fin.last n) :=
  chain_invariant h (fun s => s.profile.grades (Fin.last n))
    (by rintro _ _ ⟨_, hn, hs⟩; exact terminal_step hs hn)

theorem Protocol.Omitting.earlier {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .earlier ε a b) (i : Fin (n+1)) (hi : i ≠ Fin.last n) :
    a.profile.grades i = b.profile.grades i :=
  chain_invariant h (fun s => s.profile.grades i) (by rintro _ _ ⟨_, hn, hs⟩; exact earlier_step hs hn hi)

theorem Protocol.Omitting.spectrum {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .rewrite ε a b) :
    a.law.spectrum = b.law.spectrum :=
  chain_invariant h (fun s => s.law.spectrum)
    (by rintro _ _ ⟨_, hn, hs⟩; exact hs.spectrum_eq hn)

theorem Protocol.Omitting.law {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {a b : D.State n} (h : D.Omitting .rewrite ε a b)
    (he : a.profile.mask = b.profile.mask) : a.law = b.law := by
  have hinv : a.profile.mask ≤ b.profile.mask ∧ (a.profile.mask = b.profile.mask → a.law = b.law) := by
    clear he
    induction h with
    | refl => exact ⟨le_rfl, fun _ => rfl⟩
    | @tail u v _ hs ih =>
      obtain ⟨k, hn, hk⟩ := hs
      have hle : u.profile.mask ≤ v.profile.mask :=
        (Capabilities.le_coordinates.mp hk.profile_le).1
      refine ⟨ih.1.trans hle, fun hEq => ?_⟩
      have hm : a.profile.mask = u.profile.mask := le_antisymm ih.1 (hEq ▸ hle)
      have he' : u.profile.mask = v.profile.mask := hm.symm.trans hEq
      have hnG : k ≠ .gate := by
        intro hg
        subst k
        simp [Protocol.Step] at hk
        have hc : CapKind .gate u.profile v.profile := hk.2.1
        exact hc.1 he'
      simp only [Protocol.Step, if_neg hn, if_neg hnG] at hk
      have hLaw : u.law = v.law := hk.2.2
      exact (ih.2 hm).trans hLaw
  exact hinv.2 he

end MovingProjection
