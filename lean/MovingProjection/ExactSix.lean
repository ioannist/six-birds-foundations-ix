import MovingProjection.Effects

/-! The signed-core test for operational six-effect factorizations. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [Nonempty M] [Nonempty X] [Nonempty R]

abbrev Protocol.Chain (D : Protocol M I X R Γ Δ) (ε : ℚ) :=
  Relation.ReflTransGen (fun a b : D.State n => ∃ e, D.Step ε e a b)

def Protocol.Factorable (D : Protocol M I X R Γ Δ) (a b : D.State n) : Prop :=
  ∀ ε : ℚ, 0 < ε → D.Chain ε a b

noncomputable def Protocol.signature (D : Protocol M I X R Γ Δ)
    (p : Capabilities M X R Γ Δ n) (law : PhysicalLaw M I X R) : M × I → SignType :=
  signedCore ((D.fiber p).spectralChecks.map MonomialTest.row) (signCode (embed law.spectrum))

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R] in
theorem Protocol.Chain.profile_le {D : Protocol M I X R Γ Δ} {ε : ℚ} {a b : D.State n}
    (h : D.Chain ε a b) : a.profile ≤ b.profile := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => obtain ⟨e, he⟩ := h; exact ih.trans he.profile_le

omit [Fintype Γ] [Fintype Δ] [Nonempty M] in
theorem Protocol.signature_invariant_of_factorable
    (D : Protocol M I X R Γ Δ) {a b : D.State n} (h : D.Factorable a b) :
    D.signature a.profile a.law = D.signature a.profile b.law := by
  apply fineConnected_signedCore (bounded_of_budget_cover (spectrumBudgets_covers D.κ))
  intro ε hε
  let η := D.δ*ε/(2*(Fintype.card (X × R) : ℚ)+1)
  have hη : 0 < η := by have := D.δ_pos; unfold η; positivity
  have hchain := h η hη
  clear h
  induction hchain with
  | refl => exact .refl
  | @tail y z hy hs ih =>
    obtain ⟨e, he⟩ := hs
    by_cases hr : e = .rewrite
    · subst e
      have ⟨hp, hnear⟩ : y.profile = z.profile ∧ PhysicalNear D.kernel η y.law z.law :=
        by simpa [Protocol.Step] using he
      have hstep : (D.fiber y.profile).step D.δ D.κ D.ν D.reverse D.kernel η y.law z.law :=
        ⟨y.legal.2.2, hp ▸ z.legal.2.2, hnear⟩
      have hlocal := spectralModulus_for_physicalStep D.kernel D.δ_pos D.κ_lt_one hε hstep
      have hlaws := Capabilities.le_coordinates.mp (Protocol.Chain.profile_le hy)
      have hin := D.checks.spectralTests_mono hlaws.2.2.1 hlaws.2.2.2
      exact ih.tail ⟨⟨fun r h => hlocal.1.1 r (hin h), hlocal.1.2⟩,
        ⟨fun r h => hlocal.2.1.1 r (hin h), hlocal.2.1.2⟩, hlocal.2.2⟩
    · rwa [← he.spectrum_eq hr]

private theorem cover_in_interval {A : Type*} [PartialOrder A] {a b : A}
    {u v : Set.Icc a b} (h : u ⋖ v) : (u : A) ⋖ (v : A) := by
  refine ⟨h.1, ?_⟩
  intro z huz hzv
  let w : Set.Icc a b := ⟨z, u.2.1.trans huz.le, hzv.le.trans v.2.2⟩
  exact h.2 (show u < w from huz) (show w < v from hzv)

private theorem interval_cover_chain {A : Type*} [PartialOrder A] [Finite A] {a b : A} (h : a ≤ b) :
    Relation.ReflTransGen (fun u v : Set.Icc a b => u ⋖ v)
      (⟨a, le_rfl, h⟩ : Set.Icc a b) ⟨b, h, le_rfl⟩ := by
  classical
  letI : LocallyFiniteOrder (Set.Icc a b) :=
    LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _
  exact le_iff_reflTransGen_covBy.mp h

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R] in
private theorem exist_law_of_chain {D : Protocol M I X R Γ Δ} {ε : ℚ}
    {V : Type*} (cap : V → Capabilities M X R Γ Δ n) {rel : V → V → Prop} {x y : V}
    (h : Relation.ReflTransGen rel x y) {a : D.State n} (ha : a.profile = cap x)
    (r : ∀ u v, rel u v → ∀ s : D.State n, s.profile = cap u →
      ∃ t : D.State n, t.profile = cap v ∧
        t.law.rate = s.law.rate ∧ t.law.spectrum = s.law.spectrum ∧ ∃ e, D.Step ε e s t) :
    ∃ b : D.State n, b.profile = cap y ∧
      b.law.rate = a.law.rate ∧ b.law.spectrum = a.law.spectrum ∧ D.Chain ε a b := by
  induction h with
  | refl => exact ⟨a, ha, rfl, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨u, hu, hrt, hspec, hu'⟩ := ih
    obtain ⟨v, hv, hrt', hspec', he⟩ := r _ _ hs u hu
    exact ⟨v, hv, hrt'.trans hrt, hspec'.trans hspec, hu'.tail he⟩

omit [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R] in
private theorem gatePhase
    (D : Protocol M I X R Γ Δ) {ε : ℚ} {a c : D.State n} (hac : a.profile ≤ c.profile)
    (hg : a.profile.grades = c.profile.grades) (hl : a.profile.licenses = c.profile.licenses)
    (he : a.profile.published = c.profile.published) :
    ∃ b : D.State n, b.profile = c.profile ∧
      b.law.rate = a.law.rate ∧ b.law.spectrum = a.law.spectrum ∧ D.Chain ε a b := by
  have h : a.reached ≤ c.reached := hac
  let V := Set.Icc a.reached c.reached
  let cap (p : V) := p.1.1
  have fields (p : V) : (cap p).grades = a.profile.grades ∧
      (cap p).licenses = a.profile.licenses ∧ (cap p).published = a.profile.published := by
    obtain ⟨_, hg₁, hl₁, he₁⟩ := Capabilities.le_coordinates.mp p.2.1
    obtain ⟨_, hg₂, hl₂, he₂⟩ := Capabilities.le_coordinates.mp p.2.2
    change (∀ i, (cap p).grades i ≤ c.profile.grades i) at hg₂
    change (cap p).licenses ⊆ c.profile.licenses at hl₂
    change (cap p).published ⊆ c.profile.published at he₂
    rw [← hg] at hg₂
    rw [← hl] at hl₂
    rw [← he] at he₂
    exact ⟨funext fun i => le_antisymm (hg₂ i) (hg₁ i),
      Finset.Subset.antisymm hl₂ hl₁, Finset.Subset.antisymm he₂ he₁⟩
  apply exist_law_of_chain cap (interval_cover_chain h) rfl
  intro u v huv s hsu
  obtain ⟨law, hlaw⟩ := v.1.2
  obtain ⟨e, hne, hk⟩ := D.capKind_of_cover (cover_in_interval huv)
  have hmask : (cap u).mask ≠ (cap v).mask := by
    intro hm
    apply huv.1.ne
    apply Subtype.ext
    apply Subtype.ext
    cases u with
    | mk u hu =>
      cases v with
      | mk v hv =>
        apply Capabilities.ext
        · exact hm
        · exact (fields ⟨u,hu⟩).1.trans (fields ⟨v,hv⟩).1.symm
        · exact (fields ⟨u,hu⟩).2.1.trans (fields ⟨v,hv⟩).2.1.symm
        · exact (fields ⟨u,hu⟩).2.2.trans (fields ⟨v,hv⟩).2.2.symm
  have HE : e = .gate := by
    change CapKind e (cap u) (cap v) at hk
    cases e
    · exact (hne rfl).elim
    · rfl
    all_goals exact (hmask hk.1).elim
  subst e
  have hcap : {s.profile with mask := v.1.1.mask} = v.1.1 := by
    rw [hsu]
    exact Capabilities.ext rfl hk.2.1 hk.2.2.1 hk.2.2.2
  have hlegal := D.mask_mixture
    (show s.profile ≤ v.1.1 from hsu ▸ huv.1.le) s.legal hlaw
  let t : D.State n := ⟨v.1.1, ⟨s.law.rate,s.law.spectrum,law.register⟩, hcap ▸ hlegal⟩
  refine ⟨t, rfl, rfl, rfl, .gate, ?_⟩
  simp only [Protocol.Step, if_neg (show Effect.gate ≠ .rewrite by decide)]
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [hsu]
    exact D.cover_reached_iff.mp (cover_in_interval huv)
  · rw [hsu]
    exact hk

omit [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R] in
private theorem finalCapabilitiesPhase
    (D : Protocol M I X R Γ Δ) {ε : ℚ} {a c : D.State n} (hac : a.profile ≤ c.profile)
    (hm : a.profile.mask = c.profile.mask) (hc : a.law = c.law) :
    D.Chain ε a c := by
  have h : a.reached ≤ c.reached := hac
  let V := Set.Icc a.reached c.reached
  have hmask (p : V) : p.1.1.mask = c.profile.mask := by
    have h₁ := (Capabilities.le_coordinates.mp p.2.1).1
    have h₂ := (Capabilities.le_coordinates.mp p.2.2).1
    change p.1.1.mask.ofDual ⊆ a.profile.mask.ofDual at h₁
    rw [hm] at h₁
    exact Set.Subset.antisymm h₁ h₂
  let liftLaw (p : V) : D.State n := ⟨p.1.1, c.law, by
    obtain ⟨_, hreach⟩ := p.1.2
    exact ⟨hreach.1, hreach.2.1, (D.legal_to_earlier p.2.2 c.legal).mpr
      ((Protocol.legal_mask c.legal).trans (congrArg OrderDual.ofDual (hmask p)).symm)⟩⟩
  have hh : D.Chain ε (liftLaw ⟨a.reached, le_rfl, h⟩) (liftLaw ⟨c.reached, h, le_rfl⟩) :=
    (interval_cover_chain h).lift liftLaw (fun u v huv => by
    obtain ⟨e, hne, hk⟩ := D.capKind_of_cover (cover_in_interval huv)
    have hgate : e ≠ .gate := by
      intro H
      subst e
      exact hk.1 ((hmask u).trans (hmask v).symm)
    exact ⟨e, by
      simp only [Protocol.Step, if_neg hne, if_neg hgate]
      exact ⟨D.cover_reached_iff.mp (cover_in_interval huv), hk, rfl⟩⟩)
  have eqStart : liftLaw ⟨a.reached, le_rfl, h⟩ = a := by
    exact Protocol.State.ext rfl hc.symm
  have eqFinish : liftLaw ⟨c.reached, h, le_rfl⟩ = c := by cases c; rfl
  rw [eqStart, eqFinish] at hh
  exact hh

theorem Protocol.factorable_iff
    (D : Protocol M I X R Γ Δ) (a c : D.State n)
    (hom : ∀ r ∈ (D.fiber a.profile).rateChecks, (∑ m, r.row.lhs m) = ∑ m, r.row.rhs m)
    (pos : ∀ r ∈ (D.fiber a.profile).rateChecks, 0 < r.ratio) :
    D.Factorable a c ↔ a.profile ≤ c.profile ∧
      D.signature a.profile a.law = D.signature a.profile c.law := by
  classical
  constructor
  · intro h
    exact ⟨(h 1 (by norm_num)).profile_le, D.signature_invariant_of_factorable h⟩
  · rintro ⟨h, hs⟩ ε hε
    let p : Capabilities M X R Γ Δ n := {a.profile with mask := c.profile.mask}
    have hp : p ≤ c.profile := by
      obtain ⟨_, hg, hl, he⟩ := Capabilities.le_coordinates.mp h
      exact Capabilities.le_coordinates.mpr ⟨fun _ H => H,hg,hl,he⟩
    have hap : a.profile ≤ p :=
      Capabilities.le_coordinates.mpr ⟨(Capabilities.le_coordinates.mp h).1, fun _ => le_rfl,
        fun _ H => H, fun _ H => H⟩
    let start : D.State n := ⟨p, ⟨a.law.rate,a.law.spectrum,c.law.register⟩,
      D.mask_mixture h a.legal c.legal⟩
    have hmask : registerMask c.law.register = c.profile.mask.ofDual := Protocol.legal_mask c.legal
    let finish : D.State n := ⟨p,c.law,⟨start.legal.1,start.legal.2.1,
      (D.legal_to_earlier hp c.legal).mpr hmask⟩⟩
    obtain ⟨b, hb, hrt, hspec, hgate⟩ := gatePhase D (ε := ε) (c := start) hap rfl rfl rfl
    change b.profile = p at hb
    have bLegal : (D.fiber p).legal D.δ D.κ D.ν D.reverse b.law := by
      rw [← hb]
      exact b.legal.2.2
    have hstep := finePhysical_of_signedCore D.kernel D.δ_pos D.κ_lt_one
      (p := D.fiber p) (ν := D.ν) (rev := D.reverse) hom pos
      bLegal finish.legal.2.2
      (by change D.signature p b.law = D.signature p c.law
          simpa only [Protocol.signature, Protocol.fiber, p, hspec] using hs) ε hε
    let liftLaw (l : PhysicalLaw M I X R) : D.State n :=
      if H : (D.fiber p).legal D.δ D.κ D.ν D.reverse l then
        ⟨p,l,start.legal.1,start.legal.2.1,H⟩ else start
    have hlift : D.Chain ε (liftLaw b.law) (liftLaw c.law) := hstep.lift liftLaw (fun u v huv => by
      refine ⟨.rewrite, ?_⟩
      simpa only [Protocol.Step, liftLaw, dif_pos huv.1, dif_pos huv.2.1,
        true_and] using huv.2.2)
    have he₁ : liftLaw b.law = b := by
      rw [show liftLaw b.law =
        (⟨p,b.law,start.legal.1,start.legal.2.1,bLegal⟩ : D.State n) from dif_pos bLegal]
      exact Protocol.State.ext hb.symm rfl
    have he₂ : liftLaw c.law = finish := by simp [liftLaw, finish, dif_pos finish.legal.2.2]
    rw [he₁, he₂] at hlift
    exact hgate.trans (hlift.trans (finalCapabilitiesPhase D hp rfl rfl))

end MovingProjection
