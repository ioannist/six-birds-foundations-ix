import MovingProjection.EventExperiments

/-! Timing an irreversible test acquisition in the audited instrument. -/

namespace MovingProjection

namespace NativeExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [Nonempty M] [Nonempty X] [Nonempty R]

/-- For lawful states with `a.profile ≤ early.profile ≤ b.profile` and the
same law at `a` and `early`, compare the source-relative signed cores at
the two starting profiles. A lawful commitment from `a` to `early` supplies
the first inequality and the law equality. -/
theorem commitLate_iff (D : NativeExperiments M I X R Γ Δ)
    (a early b : D.protocol.State n) (hlaw : a.law = early.law)
    (ha : a.profile ≤ early.profile) (hb : early.profile ≤ b.profile) :
    (D.protocol.Factorable a b ∧ ¬ D.protocol.Factorable early b) ↔
      D.protocol.signature a.profile a.law = D.protocol.signature a.profile b.law ∧
      D.protocol.signature early.profile a.law ≠ D.protocol.signature early.profile b.law := by
  rw [D.exact_six_iff, D.exact_six_iff, ← hlaw]
  simp only [ha.trans hb, hb, true_and]

end NativeExperiments

namespace EventExperiments

open scoped BigOperators

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [DecidableEq X]

variable (E : EventExperiments M I X R Γ Δ)

def SameNumbers (a b : E.State n) : Prop :=
  a.val.law.rate = b.val.law.rate ∧ a.val.law.spectrum = b.val.law.spectrum

/-- Take the rates and spectrum of `s` and the support, grades and
register of `template`, using only tests already held by `s`. -/
def carry (template s : E.State n)
    (hℓ : template.val.profile.licenses ⊆ s.val.profile.licenses)
    (ha : template.val.profile.published ⊆ s.val.profile.published) : E.State n := by
  let law : PhysicalLaw M I X R := ⟨s.val.law.rate, s.val.law.spectrum, template.val.law.register⟩
  refine ⟨⟨template.val.profile, law, template.val.legal.1, template.val.legal.2.1, ?_⟩, ?_⟩
  · refine ⟨⟨s.val.legal.2.2.1.1, s.val.legal.2.2.1.2.1, ?_⟩,
      ⟨?_, s.val.legal.2.2.2.1.2⟩, template.val.legal.2.2.2.2⟩
    · exact fun r hr => s.val.legal.2.2.1.2.2 r
        (E.base.protocol.checks.rateTests_mono hℓ ha hr)
    · exact fun r hr => s.val.legal.2.2.2.1.1 r
        (E.base.protocol.checks.spectralTests_mono hℓ ha hr)
  · intro g hg w hw x y
    have hm (v : List M) : nativeWordEndpoint (law.marked E.native.parity) v x y =
        nativeWordEndpoint (s.val.law.marked E.native.parity) v x y := by
      unfold PhysicalLaw.marked
      rw [nativeWordEndpoint_factor _ _ _ _ template.val.legal.2.2.2.2.1.2.1,
        nativeWordEndpoint_factor _ _ _ _ s.val.legal.2.2.2.2.1.2.1]
    rw [hm, hm, hm]
    exact s.property g (hℓ hg) w hw x y

/-- View the target's numbers at the source profile using the source register. -/
def atSource (a b : E.State n) (h : a.val.profile ≤ b.val.profile) : E.State n :=
  let h' := Capabilities.le_coordinates.1 h
  E.carry a b h'.2.2.1 h'.2.2.2

omit [Fintype Γ] [Fintype Δ] in
private theorem state_ext {a b : E.State n}
    (hp : a.val.profile = b.val.profile) (hl : a.val.law = b.val.law) : a = b :=
  Subtype.ext (Protocol.State.ext hp hl)

def projected (s : E.State n) (j : M × X × X) : ℚ :=
  s.val.law.rate j.1 * E.native.parity.kernel (fun i => s.val.law.spectrum (j.1,i)) j.2.1 j.2.2

omit [Fintype Γ] [Fintype Δ] in
theorem projected_near [Nonempty R] {η : ℚ} (s t : E.State n)
    (h : PhysicalNear E.native.parity η s.val.law t.val.law) (j : M × X × X) :
    |E.projected s j - E.projected t j| < (Fintype.card R : ℚ) * η := by
  rcases j with ⟨m,x,y⟩
  let u : R := Classical.choice inferInstance
  have hs (P : E.State n) : ∑ j, P.val.law.marked E.native.parity m (x,u) (y,j) =
      E.projected P (m,x,y) :=
    native_projection _ _ _ _ _ _ _ _ (P.val.legal.2.2.2.2.1.2.1 m x y u)
  rw [← hs s, ← hs t, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_lt
  simpa using Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset R))
    Finset.univ_nonempty (fun j _ => h m (x,u) (y,j))

omit [Fintype Γ] [Fintype Δ] in
theorem carry_near {ε : ℚ}
    (a s t : E.State n)
    (hℓs : a.val.profile.licenses ⊆ s.val.profile.licenses)
    (has : a.val.profile.published ⊆ s.val.profile.published)
    (hℓt : a.val.profile.licenses ⊆ t.val.profile.licenses)
    (hat : a.val.profile.published ⊆ t.val.profile.published)
    (hd : ∀ j, |E.projected s j - E.projected t j| < ε) :
    PhysicalNear E.native.parity ε (E.carry a s hℓs has).val.law
      (E.carry a t hℓt hat).val.law := by
  rintro m ⟨x,u⟩ ⟨y,v⟩
  let L := a.val.law.register
  change |E.projected s (m,x,y) * L m x y u v - E.projected t (m,x,y) * L m x y u v| < ε
  have hL := a.val.legal.2.2.2.2.1
  rw [← sub_mul, abs_mul, abs_of_nonneg (hL.1 m x y u v)]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hL.entry_le_one m x y u v)).trans_lt (hd _)

omit [Fintype Γ] [Fintype Δ] in
theorem fixedProfile_registerChain [Nonempty X] {a b : E.State n} {ε : ℚ} (hε : 0 < ε)
    (hp : a.val.profile = b.val.profile) (hn : E.SameNumbers a b) : E.Chain ε a b := by
  let D := E.base.protocol
  let p := a.val.profile
  let L := a.val.law.register
  let K := b.val.law.register
  let admissible (T : Register M X R) :=
    RegisterValid D.ν D.reverse (p.grades (Fin.last n)).ofDual T ∧ registerMask T = p.mask.ofDual
  have hL : admissible L := a.val.legal.2.2.2.2
  have hK : admissible K := by
    change RegisterValid D.ν D.reverse (a.val.profile.grades (Fin.last n)).ofDual K ∧
      registerMask K = a.val.profile.mask.ofDual
    rw [hp]
    exact b.val.legal.2.2.2.2
  let liftReg (T : Register M X R) (hT : admissible T) : E.State n := by
    let temp : E.State n := by
      refine ⟨⟨p, ⟨a.val.law.rate,a.val.law.spectrum,T⟩,
        a.val.legal.1,a.val.legal.2.1,a.val.legal.2.2.1,a.val.legal.2.2.2.1,hT⟩, ?_⟩
      intro g hg w hw x y
      have he (l : List M) :
          nativeWordEndpoint ((⟨a.val.law.rate,a.val.law.spectrum,T⟩ : PhysicalLaw M I X R).marked
            E.native.parity) l x y =
          nativeWordEndpoint (a.val.law.marked E.native.parity) l x y := by
        unfold PhysicalLaw.marked
        rw [nativeWordEndpoint_factor _ _ _ _ hT.1.2.1,
          nativeWordEndpoint_factor _ _ _ _ hL.1.2.1]
      rw [he, he, he]
      exact a.property g hg w hw x y
    exact temp
  classical
  let lift (T : Register M X R) := if hT : admissible T then liftReg T hT else a
  have start : lift L = a := by
    simp only [lift, dif_pos hL]
    exact state_ext E rfl (PhysicalLaw.ext rfl rfl rfl)
  have finish : lift K = b := by
    simp only [lift, dif_pos hK]
    exact state_ext E hp (PhysicalLaw.ext hn.1 hn.2 rfl)
  rw [← start, ← finish]
  apply (register_fineConnected hL.1 hK.1 (hL.2.trans hK.2.symm) hε).lift lift
  intro U V h
  have hU : admissible U := ⟨h.1, h.2.2.1.trans hL.2⟩
  have hV : admissible V := ⟨h.2.1, h.2.2.2.1.trans hL.2⟩
  simp only [lift, dif_pos hU, dif_pos hV]
  refine Or.inl ⟨rfl, ?_⟩
  rintro m ⟨x,u⟩ ⟨y,v⟩
  let rt := a.val.law.rate m
  let Q := E.native.parity.kernel (fun i => a.val.law.spectrum (m,i)) x y
  change |rt * Q * U m x y u v - rt * Q * V m x y u v| < ε
  have hrt₀ : 0 ≤ rt := E.base.δ_pos.le.trans (a.val.legal.2.2.1.1 m)
  have hrt₁ : rt ≤ 1 := by
    change a.val.law.rate m ≤ 1
    rw [← a.val.legal.2.2.1.2.1]
    exact Finset.single_le_sum (fun j _ => E.base.δ_pos.le.trans (a.val.legal.2.2.1.1 j))
      (Finset.mem_univ m)
  have hQ := E.native.parity.kernel_bounds
    ((spectrum_budget a.val.legal.2.2.2.1 m).trans_lt E.native.κ_lt_one) x y
  rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hrt₀ hQ.1)]
  exact (mul_le_of_le_one_left (abs_nonneg _)
    ((mul_le_of_le_one_right hrt₀ hQ.2).trans hrt₁)).trans_lt (h.2.2.2.2 m x y u v)

omit [Fintype Γ] [Fintype Δ] in
private theorem cover_sameNumbers [Nonempty X] {a b : E.State n} {ε : ℚ}
    (hε : 0 < ε) (hc : E.Cover a.val.profile b.val.profile)
    (hn : E.SameNumbers a b) : E.Chain ε a b := by
  by_cases hm : a.val.profile.mask = b.val.profile.mask
  · let p := a.val.profile
    let l := b.val.law
    let D := E.base.protocol
    let c : E.State n := ⟨⟨p, l, a.val.legal.1, a.val.legal.2.1,
      (D.legal_to_earlier hc.1.le b.val.legal).2
        ((Protocol.legal_mask b.val.legal).trans (congrArg OrderDual.ofDual hm.symm))⟩,
      fun g hg => b.property g ((Capabilities.le_coordinates.1 hc.1.le).2.2.1 hg)⟩
    exact (E.fixedProfile_registerChain hε (a := a) (b := c) rfl hn).tail
      (Or.inr ⟨hc, Or.inl ⟨hm,rfl⟩⟩)
  · exact .single (Or.inr ⟨hc, Or.inr ⟨hm, hn⟩⟩)

private abbrev Attained (E : EventExperiments M I X R Γ Δ) (n : ℕ) :=
  {p : Capabilities M X R Γ Δ n // ∃ l, E.base.protocol.legal p l ∧ E.holds p l}

private def reached (a : E.State n) : E.Attained n :=
  ⟨a.val.profile, a.val.law, a.val.legal, a.property⟩

omit [Fintype Γ] [Fintype Δ] in
private theorem cover_reached {p q : E.Attained n} (h : p ⋖ q) : E.Cover p.val q.val := by
  refine ⟨h.1, ?_⟩
  intro r hr hpr hrq
  let v : E.Attained n := ⟨r,hr⟩
  exact h.2 (show p < v from hpr) (show v < q from hrq)

/-- If the source profile is at most the target profile and the two lawful
states have the same rates and probe responses, they admit a chain at every
positive tolerance, including when support shrinks. -/
theorem chain_of_sameNumbers [Nonempty X] {a b : E.State n} {ε : ℚ}
    (hε : 0 < ε) (hab : a.val.profile ≤ b.val.profile) (hn : E.SameNumbers a b) :
    E.Chain ε a b := by
  let ap := E.reached a
  let bp := E.reached b
  classical
  letI : LocallyFiniteOrder (E.Attained n) :=
    LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _
  have covers : Relation.ReflTransGen (fun u v : E.Attained n => u ⋖ v) ap bp :=
    le_iff_reflTransGen_covBy.mp hab
  have lift (p : E.Attained n) (hp : p ≤ bp) : ∃ c : E.State n,
      E.reached c = p ∧ E.SameNumbers c b := by
    obtain ⟨l, hl, ht⟩ := p.property
    let template : E.State n := ⟨⟨p.val,l,hl⟩, ht⟩
    let c : E.State n := E.atSource template b hp
    exact ⟨c, Subtype.ext rfl, ⟨rfl,rfl⟩⟩
  have assemble (p : E.Attained n)
      (hh : Relation.ReflTransGen (fun u v : E.Attained n => u ⋖ v) ap p) :
      ∀ c : E.State n, E.reached c = p → E.SameNumbers c b → p ≤ bp → E.Chain ε a c := by
    induction hh with
    | refl =>
      intro c hc hcn _
      exact E.fixedProfile_registerChain hε (congrArg Subtype.val hc).symm
        ⟨hn.1.trans hcn.1.symm, hn.2.trans hcn.2.symm⟩
    | @tail u v _ huv ih =>
      intro c hc hcn hle
      have hu := huv.1.le.trans hle
      obtain ⟨d, hd, hdn⟩ := lift u hu
      have hcov := E.cover_reached huv
      rw [← hd, ← hc] at hcov
      exact (ih d hd hdn hu).trans
        (E.cover_sameNumbers hε hcov ⟨hdn.1.trans hcn.1.symm, hdn.2.trans hcn.2.symm⟩)
  exact assemble bp covers b rfl ⟨rfl,rfl⟩ le_rfl

/-- All rate and probe-response revisions can take place at the source
profile when it precedes or equals the target profile. The projection uses
the source register. The later profile phase can include register rewrites. -/
theorem factorable_iff_atSource [Nonempty X] [Nonempty R] (a b : E.State n)
    (hab : a.val.profile ≤ b.val.profile) :
    E.Factorable a b ↔ E.Factorable a (E.atSource a b hab) := by
  constructor
  · intro H ε hε
    let η := ε / ((Fintype.card R : ℚ) + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    have hbound : (Fintype.card R : ℚ) * η ≤ ε := by
      have he : ((Fintype.card R : ℚ) + 1) * η = ε := by
        dsimp [η]
        field_simp
      linarith
    have map (s : E.State n) (h : E.Chain η a s) :
        E.Chain ε a (E.atSource a s h.profile_le) := by
      induction h with
      | refl =>
        have he : E.atSource a a le_rfl = a := state_ext E rfl (PhysicalLaw.ext rfl rfl rfl)
        exact he ▸ Relation.ReflTransGen.refl
      | @tail s t h hs ih =>
        have has := Capabilities.le_coordinates.1 (Chain.profile_le h)
        have hat := Capabilities.le_coordinates.1 ((Chain.profile_le h).trans hs.profile_le)
        rcases hs with (⟨_, hn⟩ | ⟨_, hs⟩)
        · exact ih.tail (Or.inl ⟨rfl,
            E.carry_near a s t has.2.2.1 has.2.2.2 hat.2.2.1 hat.2.2.2
              (fun j => (E.projected_near s t hn j).trans_le hbound)⟩)
        · have hst : E.SameNumbers s t := hs.elim
            (fun h => ⟨congrArg PhysicalLaw.rate h.2, congrArg PhysicalLaw.spectrum h.2⟩)
            And.right
          have he : E.carry a s has.2.2.1 has.2.2.2 =
              E.carry a t hat.2.2.1 hat.2.2.2 :=
            state_ext E rfl (PhysicalLaw.ext hst.1 hst.2 rfl)
          change E.Chain ε a (E.carry a t hat.2.2.1 hat.2.2.2)
          rw [← he]
          exact ih
    exact map b (H η hη)
  · intro H ε hε
    exact (H ε hε).trans (E.chain_of_sameNumbers hε hab ⟨rfl,rfl⟩)

/-- For an attainable intermediate profile, once the target numbers can
be reached it is possible to adopt that profile with those numbers. -/
theorem commitAtTargetNumbers [Nonempty X] [Nonempty R] (a b template : E.State n)
    (ha : a.val.profile ≤ template.val.profile) (hb : template.val.profile ≤ b.val.profile)
    (h : E.Factorable a b) :
    ∃ c : E.State n, c.val.profile = template.val.profile ∧ E.SameNumbers c b ∧
      E.Factorable a c ∧ E.Factorable c b := by
  let c := E.atSource template b hb
  refine ⟨c, rfl, ⟨rfl,rfl⟩, ?_, fun ε hε => E.chain_of_sameNumbers hε hb ⟨rfl,rfl⟩⟩
  have he : E.atSource a c ha = E.atSource a b (ha.trans hb) :=
    state_ext E rfl (PhysicalLaw.ext rfl rfl rfl)
  apply (E.factorable_iff_atSource a c ha).2
  rw [he]
  exact (E.factorable_iff_atSource a b (ha.trans hb)).1 h

/-- If the intermediate profile has the target support, the entire target
law can be in place at commitment. -/
theorem commitAtTarget [Nonempty X] [Nonempty R] (a b template : E.State n)
    (ha : a.val.profile ≤ template.val.profile) (hb : template.val.profile ≤ b.val.profile)
    (hm : template.val.profile.mask = b.val.profile.mask) (h : E.Factorable a b) :
    ∃ c : E.State n, c.val.profile = template.val.profile ∧ c.val.law = b.val.law ∧
      E.Factorable a c ∧ E.Factorable c b := by
  let p := template.val.profile
  let D := E.base.protocol
  let t : E.State n := ⟨⟨p, b.val.law, template.val.legal.1, template.val.legal.2.1,
    (D.legal_to_earlier hb b.val.legal).2 (hm ▸ Protocol.legal_mask b.val.legal)⟩,
    fun g hg => b.property g ((Capabilities.le_coordinates.1 hb).2.2.1 hg)⟩
  refine ⟨t,rfl,rfl,?_,fun ε hε => E.chain_of_sameNumbers hε hb ⟨rfl,rfl⟩⟩
  have he : E.atSource a t ha = E.atSource a b (ha.trans hb) :=
    state_ext E rfl (PhysicalLaw.ext rfl rfl rfl)
  apply (E.factorable_iff_atSource a t ha).2
  rw [he]
  exact (E.factorable_iff_atSource a b (ha.trans hb)).1 h

/-- A prescribed monotone family of attained profiles between the endpoints
can be visited in order after putting the rates and responses at their target
values. Each consecutive transition is finely reachable. -/
theorem commitAtTargetNumbersAlong [Nonempty X] [Nonempty R] {ι : Type*} [Preorder ι]
    (a b : E.State n) (template : ι → E.State n)
    (hmono : Monotone fun i => (template i).val.profile)
    (ha : ∀ i, a.val.profile ≤ (template i).val.profile)
    (hb : ∀ i, (template i).val.profile ≤ b.val.profile)
    (h : E.Factorable a b) :
    ∃ stage : ι → E.State n,
      (∀ i, (stage i).val.profile = (template i).val.profile ∧ E.SameNumbers (stage i) b ∧
        E.Factorable a (stage i) ∧ E.Factorable (stage i) b) ∧
      ∀ i j, i ≤ j → E.Factorable (stage i) (stage j) := by
  choose stage hp hn hstart hend using fun i =>
    E.commitAtTargetNumbers a b (template i) (ha i) (hb i) h
  refine ⟨stage, fun i => ⟨hp i, hn i, hstart i, hend i⟩, ?_⟩
  intro i j hij ε hε
  have hle : (stage i).val.profile ≤ (stage j).val.profile := by
    rw [hp i, hp j]
    exact hmono hij
  exact E.chain_of_sameNumbers hε hle
    ⟨(hn i).1.trans (hn j).1.symm, (hn i).2.trans (hn j).2.symm⟩

end EventExperiments

end MovingProjection
