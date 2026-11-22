import MovingProjection.FixedProfile
import MovingProjection.RouteTests
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Interval.Finset.Basic

/-! Observable edit capabilities and their induced finite order. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I]

@[ext] structure Capabilities (M X R Γ Δ : Type*) (n : ℕ) where
  mask : (Set (Proposal M X R))ᵒᵈ
  grades : Fin (n+1) → (Setoid R)ᵒᵈ
  licenses : Finset Γ
  published : Finset Δ

namespace Capabilities

private def coordinates (p : Capabilities M X R Γ Δ n) :=
  (p.mask, p.grades, p.licenses, p.published)

instance : PartialOrder (Capabilities M X R Γ Δ n) :=
  PartialOrder.lift coordinates (by
    rintro ⟨m,f,r,e⟩ ⟨m',f',r',e'⟩ h
    cases h
    rfl)

omit [Fintype M] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ] [DecidableEq M] in
theorem le_coordinates {p q : Capabilities M X R Γ Δ n} :
    p ≤ q ↔ q.mask.ofDual ⊆ p.mask.ofDual ∧
      (∀ i, (q.grades i).ofDual ≤ (p.grades i).ofDual) ∧
      p.licenses ⊆ q.licenses ∧ p.published ⊆ q.published :=
  Iff.rfl

private local instance [Finite R] : Finite (Setoid R) :=
  Finite.of_injective (fun f : Setoid R => {p : R × R | f.r p.1 p.2})
    (by
      intro f g h
      exact Setoid.ext fun u v => Set.ext_iff.mp h (u,v))

instance [Finite M] [Finite X] [Finite R] [Finite Γ] [Finite Δ] :
    Finite (Capabilities M X R Γ Δ n) :=
  Finite.of_injective coordinates (by
    rintro ⟨m,f,r,e⟩ ⟨m',f',r',e'⟩ h
    cases h
    rfl)

def nested (p : Capabilities M X R Γ Δ n) : Prop :=
  Monotone p.grades

end Capabilities

structure ProbeCatalog (M I Γ Δ : Type*) where
  licenseRate : Γ → List (MonomialTest M)
  licenseSpectrum : Γ → List (MonomialTest (M × I))
  auditRate : Δ → List (MonomialTest M)
  auditSpectrum : Δ → List (MonomialTest (M × I))
  reversal : List (MonomialTest (M × I))
  licensePolicy : Finset Γ → Prop

noncomputable def ProbeCatalog.rateTests (d : ProbeCatalog M I Γ Δ)
    (ℓ : Finset Γ) (e : Finset Δ) : List (MonomialTest M) :=
  ℓ.toList.flatMap d.licenseRate ++ e.toList.flatMap d.auditRate

noncomputable def ProbeCatalog.spectralTests (d : ProbeCatalog M I Γ Δ)
    (ℓ : Finset Γ) (e : Finset Δ) : List (MonomialTest (M × I)) :=
  d.reversal ++ ℓ.toList.flatMap d.licenseSpectrum ++ e.toList.flatMap d.auditSpectrum

omit [Fintype M] [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq I] in
theorem ProbeCatalog.rateTests_mono (d : ProbeCatalog M I Γ Δ)
    {ℓ k : Finset Γ} {e f : Finset Δ} (hℓ : ℓ ⊆ k) (he : e ⊆ f) :
    d.rateTests ℓ e ⊆ d.rateTests k f := by
  intro r hr
  simp only [rateTests, List.mem_append, List.mem_flatMap, Finset.mem_toList] at hr ⊢
  rcases hr with ⟨g,hg,hr⟩ | ⟨a,ha,hr⟩
  · exact Or.inl ⟨g, hℓ hg, hr⟩
  · exact Or.inr ⟨a, he ha, hr⟩

omit [Fintype M] [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq I] in
theorem ProbeCatalog.spectralTests_mono (d : ProbeCatalog M I Γ Δ)
    {ℓ k : Finset Γ} {e f : Finset Δ} (hℓ : ℓ ⊆ k) (he : e ⊆ f) :
    d.spectralTests ℓ e ⊆ d.spectralTests k f := by
  intro r hr
  simp only [spectralTests, List.mem_append, List.mem_flatMap, Finset.mem_toList] at hr ⊢
  rcases hr with (hr | ⟨g,hg,hr⟩) | ⟨a,ha,hr⟩
  · exact Or.inl (Or.inl hr)
  · exact Or.inl (Or.inr ⟨g, hℓ hg, hr⟩)
  · exact Or.inr ⟨a, he ha, hr⟩

structure Protocol (M I X R Γ Δ : Type*) [Fintype X] [DecidableEq I] where
  kernel : ParityBasis I X
  ν : R → ℚ
  reverse : M → M
  δ : ℚ
  κ : ℚ
  δ_pos : 0 < δ
  κ_lt_one : κ < 1
  checks : ProbeCatalog M I Γ Δ

noncomputable def Protocol.fiber (D : Protocol M I X R Γ Δ)
    (p : Capabilities M X R Γ Δ n) : FixedProfile M I X R :=
  ⟨D.checks.rateTests p.licenses p.published, D.checks.spectralTests p.licenses p.published,
    (p.grades (Fin.last n)).ofDual, p.mask.ofDual⟩

def Protocol.legal (D : Protocol M I X R Γ Δ) (p : Capabilities M X R Γ Δ n)
    (a : PhysicalLaw M I X R) : Prop :=
  p.nested ∧ D.checks.licensePolicy p.licenses ∧
    (D.fiber p).legal D.δ D.κ D.ν D.reverse a

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
theorem Protocol.legal_mask {D : Protocol M I X R Γ Δ}
    {p : Capabilities M X R Γ Δ n} {a : PhysicalLaw M I X R} (h : D.legal p a) :
    registerMask a.register = p.mask.ofDual :=
  h.2.2.2.2.2

omit [Fintype Γ] [Fintype Δ] [DecidableEq M] in
theorem Protocol.legal_to_earlier (D : Protocol M I X R Γ Δ)
    {p q : Capabilities M X R Γ Δ n} (h : p ≤ q)
    {a : PhysicalLaw M I X R} (ha : D.legal q a) :
    (D.fiber p).legal D.δ D.κ D.ν D.reverse a ↔ registerMask a.register = p.mask.ofDual := by
  obtain ⟨_, hgrade, hlicense, haudit⟩ := Capabilities.le_coordinates.mp h
  constructor
  · exact fun hp => hp.2.2.2
  · intro hm
    let hq := ha.2.2
    refine ⟨⟨hq.1.1, hq.1.2.1, ?_⟩, ⟨?_, hq.2.1.2⟩, ?_, hm⟩
    · exact fun r hr => hq.1.2.2 r (D.checks.rateTests_mono hlicense haudit hr)
    · exact fun r hr => hq.2.1.1 r (D.checks.spectralTests_mono hlicense haudit hr)
    · exact hq.2.2.1.coarsen (hgrade (Fin.last n))

end MovingProjection
