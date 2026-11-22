import MovingProjection.WitnessInput
import MovingProjection.ReadoutChains

/-! Finite deterministic execution of the example's new audit query. -/

namespace MovingProjection.Example

inductive CalibrationConfig
  | loaded
  | accepted
  | rejected
  deriving DecidableEq, Fintype

abbrev Measured := Mark → Bool × Cell → Bool × Cell → ℚ

def calibrationPreparation : Bool × Cell := (false,0)

def calibrationStep (P : Measured) : CalibrationConfig → CalibrationConfig
  | .loaded =>
    if observedSignal parity P 2 calibrationPreparation () =
        observedRate P 2 calibrationPreparation * (1/8) then .accepted else .rejected
  | .accepted => .accepted
  | .rejected => .rejected

def calibrationTrace : Fin 2 → CalibrationConfig
  | 0 => .loaded
  | 1 => .accepted

/-- The exact replay formula of the two-entry trace. Its output is a
configuration in a finite deterministic carrier. -/
def CalibrationReplay (F : CalibrationConfig → CalibrationConfig) : Prop :=
  calibrationTrace 1 = F (calibrationTrace 0)

theorem calibration_replay_iff (s : State) :
    CalibrationReplay (calibrationStep (experiment.readouts s).trial) ↔
      s.law.spectrum (2,()) = 1/8 := by
  have hRate : observedRate (experiment.readouts s).trial 2 calibrationPreparation =
      s.law.rate 2 := by
    let a (m : Mark) (i : Unit) := s.law.spectrum (m,i)
    let P := nativeMarked parity a s.law.rate s.law.register
    change observedRate P 2 calibrationPreparation = _
    exact observedRate_native parity a _ _ s.legal.2.2.2.2.1.2.1 _ _
  have hSpec := experiment.readouts_spectrum s calibrationPreparation 2 ()
  rw [hRate] at hSpec
  have hNonzero : s.law.rate 2 ≠ 0 :=
    (experiment.δ_pos.trans_le (s.legal.2.2.1.1 2)).ne'
  change CalibrationConfig.accepted =
    (if observedSignal parity (experiment.readouts s).trial 2 calibrationPreparation () =
        observedRate (experiment.readouts s).trial 2 calibrationPreparation * (1/8)
      then CalibrationConfig.accepted else CalibrationConfig.rejected) ↔ _
  have he : observedSignal parity (experiment.readouts s).trial 2 calibrationPreparation () =
      s.law.spectrum (2,()) * s.law.rate 2 :=
    (div_eq_iff hNonzero).mp hSpec
  rw [he, hRate, mul_comm (s.law.rate 2) (1/8)]
  by_cases h : s.law.spectrum (2,()) = 1/8
  · simp [h]
  · have h' : s.law.spectrum (2,()) * s.law.rate 2 ≠ 1/8 * s.law.rate 2 :=
      fun he => h (mul_right_cancel₀ hNonzero he)
    rw [if_neg h']
    constructor
    · intro hh
      cases hh
    · exact fun hh => (h hh).elim

theorem matches_newly_published_query :
    CalibrationReplay (calibrationStep (experiment.readouts licensed).trial) ∧
      calibrationStep (experiment.readouts licensed).trial =
        calibrationStep (experiment.readouts published).trial ∧
      ¬ (experiment.readouts licensed).cited true ∧
        (experiment.readouts published).cited true := by
  refine ⟨(calibration_replay_iff licensed).mpr rfl,rfl,publication_cites_actual_calibration⟩

theorem replay_fails_before_rewrite :
    ¬ CalibrationReplay (calibrationStep (experiment.readouts gated).trial) := by
  rw [calibration_replay_iff]
  change ¬ ((-1/8 : ℚ) = 1/8)
  norm_num

end MovingProjection.Example
