import MovingProjection.Rates
import MovingProjection.Register

/-! The signed criterion on a fixed physical capability profile. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R : Type*} [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq M] [DecidableEq I] [Nonempty M] [Nonempty X] [Nonempty R]

@[ext] structure PhysicalLaw (M I X R : Type*) where
  rate : M → ℚ
  spectrum : M × I → ℚ
  register : Register M X R

def PhysicalLaw.marked (a : PhysicalLaw M I X R) (b : ParityBasis I X)
    (m : M) (s t : X × R) : ℚ :=
  nativeMarked b (fun m i => a.spectrum (m,i)) a.rate a.register m s t

private def markEmbedding (m : M) : I ↪ M × I :=
  ⟨fun i => (m,i), fun _ _ h => congrArg Prod.snd h⟩

noncomputable def spectrumBudgets (κ : ℚ) : List (MarkBudget (M × I)) :=
  Finset.univ.toList.map fun m : M =>
    ⟨Finset.univ.map (markEmbedding m), κ⟩

omit [DecidableEq M] [DecidableEq I] [Nonempty M] in
theorem spectrumBudgets_covers (κ : ℚ) (e : M × I) :
    ∃ b ∈ spectrumBudgets κ, e ∈ b.indices := by
  rcases e with ⟨m,i⟩
  let s : MarkBudget (M × I) := ⟨Finset.univ.map (markEmbedding m), κ⟩
  refine ⟨s, List.mem_map.mpr ⟨m, by simp, rfl⟩, ?_⟩
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

omit [DecidableEq M] [DecidableEq I] [Nonempty M] in
theorem spectrum_budget {κ : ℚ} {tests : List (MonomialTest (M × I))} {a : M × I → ℚ}
    (h : Legal tests (spectrumBudgets κ) a) (m : M) :
    ∑ i, |a (m,i)| ≤ κ := by
  let s : MarkBudget (M × I) := ⟨Finset.univ.map (markEmbedding m), κ⟩
  have hs : s ∈ spectrumBudgets κ := List.mem_map.mpr ⟨m, by simp, rfl⟩
  simpa [s, Finset.sum_map, markEmbedding] using h.2 s hs

structure FixedProfile (M I X R : Type*) where
  rateChecks : List (MonomialTest M)
  spectralChecks : List (MonomialTest (M × I))
  observation : Setoid R
  mask : Set (Proposal M X R)

def FixedProfile.legal (p : FixedProfile M I X R) (δ κ : ℚ) (ν : R → ℚ) (rev : M → M)
    (a : PhysicalLaw M I X R) : Prop :=
  RateLegal δ p.rateChecks a.rate ∧
    Legal p.spectralChecks (spectrumBudgets κ) a.spectrum ∧
    RegisterValid ν rev p.observation a.register ∧
    registerMask a.register = p.mask

def PhysicalNear (b : ParityBasis I X) (ε : ℚ) (a c : PhysicalLaw M I X R) : Prop :=
  ∀ m s t, |a.marked b m s t - c.marked b m s t| < ε

def FixedProfile.step (p : FixedProfile M I X R) (δ κ : ℚ) (ν : R → ℚ) (rev : M → M)
    (b : ParityBasis I X) (ε : ℚ) (a c : PhysicalLaw M I X R) : Prop :=
  p.legal δ κ ν rev a ∧ p.legal δ κ ν rev c ∧ PhysicalNear b ε a c

omit [DecidableEq M] [Nonempty M] in
theorem spectralModulus_for_physicalStep
    (b : ParityBasis I X) {δ κ ε : ℚ} (hδ : 0 < δ) (hκ : κ < 1) (hε : 0 < ε)
    {p : FixedProfile M I X R} {ν : R → ℚ} {rev : M → M} {a c : PhysicalLaw M I X R}
    (h : p.step δ κ ν rev b (δ*ε/(2*(Fintype.card (X × R) : ℚ)+1)) a c) :
    LocalStep p.spectralChecks (spectrumBudgets κ) ε a.spectrum c.spectrum := by
  refine ⟨h.1.2.1, h.2.1.2.1, ?_⟩
  rintro ⟨m,i⟩
  let s : X × R := Classical.choice inferInstance
  have hb : |c.spectrum (m,i)| ≤ 1 := (Finset.single_le_sum
    (s := (Finset.univ : Finset I)) (fun j _ => abs_nonneg (c.spectrum (m,j)))
    (Finset.mem_univ i)).trans ((spectrum_budget h.2.1.2.1 m).trans hκ.le)
  have H := native_spectral_modulus b (fun m i => a.spectrum (m,i)) (fun m i => c.spectrum (m,i))
    a.rate c.rate a.register c.register h.1.2.2.1.2.1 h.2.1.2.2.1.2.1
    m s i hδ (h.1.1.1 m) hb (fun t => (h.2.2 m s t).le)
  apply H.trans_lt
  have hN : 0 ≤ (Fintype.card (X × R) : ℚ) := by positivity
  have hden : 0 < 2*(Fintype.card (X × R) : ℚ)+1 := by positivity
  apply (div_lt_iff₀ hδ).2
  rw [mul_comm (2 * (Fintype.card (X × R) : ℚ)), div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).2
  nlinarith

omit [Nonempty M] in
theorem finePhysical_signedCore
    (b : ParityBasis I X) {δ κ : ℚ} (hδ : 0 < δ) (hκ : κ < 1)
    {p : FixedProfile M I X R} {ν : R → ℚ} {rev : M → M} {a c : PhysicalLaw M I X R}
    (h : ∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (p.step δ κ ν rev b ε) a c) :
    signedCore (p.spectralChecks.map MonomialTest.row) (signCode (embed a.spectrum)) =
      signedCore (p.spectralChecks.map MonomialTest.row) (signCode (embed c.spectrum)) := by
  apply fineConnected_signedCore (bounded_of_budget_cover (spectrumBudgets_covers κ))
  intro ε hε
  have hη : 0 < δ*ε/(2*(Fintype.card (X × R) : ℚ)+1) := by positivity
  exact (h _ hη).lift PhysicalLaw.spectrum
    (fun _ _ hs => spectralModulus_for_physicalStep b hδ hκ hε hs)

namespace ParityBasis

omit [Fintype M] [Fintype R] [DecidableEq M] [Nonempty M] [Nonempty R] in
theorem kernel_bounds (b : ParityBasis I X) {spectrum : I → ℚ}
    (h : (∑ i, |spectrum i|) < 1) (x y : X) :
    0 ≤ b.kernel spectrum x y ∧ b.kernel spectrum x y ≤ 1 := by
  refine ⟨(b.kernel_pos spectrum h x y).le, ?_⟩
  rw [← b.kernel_row_sum spectrum x]
  exact Finset.single_le_sum (fun j _ => (b.kernel_pos spectrum h x j).le) (Finset.mem_univ y)

omit [Fintype M] [Fintype R] [DecidableEq M] [Nonempty M] [Nonempty R] in
theorem kernel_sub_le (b : ParityBasis I X) {a c : I → ℚ} {η : ℚ}
    (h : ∀ i, |a i - c i| ≤ η) (x y : X) :
    |b.kernel a x y - b.kernel c x y| ≤ (Fintype.card I : ℚ)*η := by
  have hX : (1 : ℚ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
  have H : 0 < (Fintype.card X : ℚ) := zero_lt_one.trans_le hX
  unfold kernel
  rw [← sub_div, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, abs_div, abs_of_pos H]
  apply (div_le_iff₀ H).2
  simp only [← sub_mul]
  have bound : (∑ i, |((a i - c i) * b.value i x) * b.value i y|) ≤
      (Fintype.card I : ℚ)*η := by
    simp only [abs_mul, b.abs_eq_one, mul_one]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => h i)
  apply ((Finset.abs_sum_le_sum_abs _ _).trans bound).trans
  have hz : 0 ≤ (Fintype.card I : ℚ)*η := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans bound
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hX hz

end ParityBasis

omit [DecidableEq M] [Nonempty M] in
private theorem rate_bound {δ : ℚ} {tests : List (MonomialTest M)} {a : M → ℚ}
    (hδ : 0 < δ) (h : RateLegal δ tests a) (m : M) :
    0 ≤ a m ∧ a m ≤ 1 := by
  refine ⟨hδ.le.trans (h.1 m), ?_⟩
  rw [← h.2.1]
  exact Finset.single_le_sum (fun k _ => hδ.le.trans (h.1 k)) (Finset.mem_univ m)

private theorem norm_product_bound {a b c : ℚ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a*b*c| ≤ |c| := by
  rw [abs_mul, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _)
    ((mul_le_of_le_one_right (abs_nonneg _) hb).trans ha)

omit [Nonempty R] in
theorem finePhysical_of_signedCore
    (b : ParityBasis I X) {δ κ : ℚ} (hδ : 0 < δ) (hκ : κ < 1)
    {p : FixedProfile M I X R} {ν : R → ℚ} {rev : M → M} {a c : PhysicalLaw M I X R}
    (hom : ∀ r ∈ p.rateChecks, (∑ m, r.row.lhs m) = ∑ m, r.row.rhs m)
    (pos : ∀ r ∈ p.rateChecks, 0 < r.ratio)
    (ha : p.legal δ κ ν rev a) (hc : p.legal δ κ ν rev c)
    (he : signedCore (p.spectralChecks.map MonomialTest.row) (signCode (embed a.spectrum)) =
      signedCore (p.spectralChecks.map MonomialTest.row) (signCode (embed c.spectrum))) :
    ∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (p.step δ κ ν rev b ε) a c := by
  intro ε hε
  have htables := register_fineConnected ha.2.2.1 hc.2.2.1 (ha.2.2.2.trans hc.2.2.2.symm) hε
  let setRegister (L : Register M X R) : PhysicalLaw M I X R := ⟨a.rate, a.spectrum, L⟩
  have h1 : Relation.ReflTransGen (p.step δ κ ν rev b ε)
      a (setRegister c.register) := by
    apply htables.lift setRegister
    intro L K h
    refine ⟨⟨ha.1, ha.2.1, h.1, h.2.2.1.trans ha.2.2.2⟩,
      ⟨ha.1, ha.2.1, h.2.1, h.2.2.2.1.trans ha.2.2.2⟩, ?_⟩
    rintro m ⟨x,u⟩ ⟨y,v⟩
    change |a.rate m * b.kernel (fun i => a.spectrum (m,i)) x y * L m x y u v -
      a.rate m * b.kernel (fun i => a.spectrum (m,i)) x y * K m x y u v| < ε
    rw [← mul_sub]
    have hrate := rate_bound hδ ha.1 m
    have hb := b.kernel_bounds ((spectrum_budget ha.2.1 m).trans_lt hκ) x y
    exact (norm_product_bound (by rw [abs_of_nonneg hrate.1]; exact hrate.2)
      (by rw [abs_of_nonneg hb.1]; exact hb.2)).trans_lt (h.2.2.2.2 m x y u v)
  let setRate (θ : M → ℚ) : PhysicalLaw M I X R := ⟨θ, a.spectrum, c.register⟩
  have h2 : Relation.ReflTransGen (p.step δ κ ν rev b ε)
      (setRegister c.register) (setRate c.rate) := by
    apply (rate_fineConnected hδ hom pos ha.1 hc.1 ε hε).lift setRate
    intro θ η h
    refine ⟨⟨h.1, ha.2.1, hc.2.2⟩, ⟨h.2.1, ha.2.1, hc.2.2⟩, ?_⟩
    rintro m ⟨x,u⟩ ⟨y,v⟩
    let Q := b.kernel (fun i => a.spectrum (m,i)) x y
    let L := c.register m x y u v
    change |θ m * Q * L - η m * Q * L| < ε
    have hcancel : θ m * Q * L - η m * Q * L = Q*L*(θ m - η m) := by ring
    rw [hcancel]
    have hb := b.kernel_bounds ((spectrum_budget ha.2.1 m).trans_lt hκ) x y
    have hk : |L| ≤ 1 := by
      rw [abs_of_nonneg (hc.2.2.1.1 _ _ _ _ _)]
      exact hc.2.2.1.entry_le_one _ _ _ _ _
    exact (norm_product_bound (by rw [abs_of_nonneg hb.1]; exact hb.2) hk).trans_lt (h.2.2 m)
  let setSpectrum (d : M × I → ℚ) : PhysicalLaw M I X R := ⟨c.rate, d, c.register⟩
  let η := ε / ((Fintype.card I : ℚ)+1)
  have hη : 0 < η := by unfold η; positivity
  have hspectra := (fineConnected_iff_signedCore ha.2.1 hc.2.1
    (bounded_of_budget_cover (spectrumBudgets_covers κ))).mpr he
  have h3 : Relation.ReflTransGen (p.step δ κ ν rev b ε)
      (setRate c.rate) c := by
    apply (hspectra η hη).lift setSpectrum
    intro u v h
    refine ⟨⟨hc.1, h.1, hc.2.2⟩, ⟨hc.1, h.2.1, hc.2.2⟩, ?_⟩
    rintro m ⟨x,s⟩ ⟨y,t⟩
    let L := c.register m x y s t
    let Q := b.kernel (fun i => u (m,i)) x y
    let U := b.kernel (fun i => v (m,i)) x y
    change |c.rate m * Q * L - c.rate m * U * L| < ε
    have hcancel : c.rate m * Q * L - c.rate m * U * L = c.rate m * L * (Q-U) := by ring
    rw [hcancel]
    have hrate := rate_bound hδ hc.1 m
    have hk : |L| ≤ 1 := by
      rw [abs_of_nonneg (hc.2.2.1.1 _ _ _ _ _)]
      exact hc.2.2.1.entry_le_one _ _ _ _ _
    have H := (norm_product_bound (by rw [abs_of_nonneg hrate.1]; exact hrate.2) hk).trans
      (b.kernel_sub_le (fun i => (h.2.2 (m,i)).le) x y)
    apply H.trans_lt
    have hηeq : ((Fintype.card I : ℚ)+1) * η = ε := by
      unfold η
      field_simp
    linarith
  exact h1.trans (h2.trans h3)

theorem finePhysical_iff_signedCore
    (b : ParityBasis I X) {δ κ : ℚ} (hδ : 0 < δ) (hκ : κ < 1)
    {p : FixedProfile M I X R} {ν : R → ℚ} {rev : M → M} {a c : PhysicalLaw M I X R}
    (hom : ∀ r ∈ p.rateChecks, (∑ m, r.row.lhs m) = ∑ m, r.row.rhs m)
    (pos : ∀ r ∈ p.rateChecks, 0 < r.ratio)
    (ha : p.legal δ κ ν rev a) (hc : p.legal δ κ ν rev c) :
    (∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (p.step δ κ ν rev b ε) a c) ↔
    signedCore (p.spectralChecks.map MonomialTest.row) (signCode (embed a.spectrum)) =
      signedCore (p.spectralChecks.map MonomialTest.row) (signCode (embed c.spectrum)) :=
  ⟨finePhysical_signedCore b hδ hκ, finePhysical_of_signedCore b hδ hκ hom pos ha hc⟩

end MovingProjection
