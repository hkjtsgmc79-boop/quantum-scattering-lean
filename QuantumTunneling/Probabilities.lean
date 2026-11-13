/- Q2: probabilities derived as incident/outgoing flux ratios. -/
import QuantumTunneling.Matching

noncomputable section
namespace QuantumTunneling
namespace Spectral

/-- The exit-anchored transmitted amplitude is 1. These are ratios, not postulated formulas. -/
def transmission (s : Spectral) : ℝ := 1 / absSq s.incidentAmplitude
def reflection (s : Spectral) : ℝ := absSq s.reflectedAmplitude / absSq s.incidentAmplitude

def transmissionAmplitude (s : Spectral) : ℂ := 1 / s.incidentAmplitude
def reflectionAmplitude (s : Spectral) : ℂ := s.reflectedAmplitude / s.incidentAmplitude

lemma denominator_gt_one (s : Spectral) : 1 < absSq s.incidentAmplitude := by
  rw [s.incident_norm_formula]
  have hs : 0 < Real.sinh (s.κ * s.a) := Real.sinh_pos_iff.2 (mul_pos s.κ_pos s.a_pos)
  have hσ := s.sigma_pos
  have hprod : 0 < s.sigma ^ 2 * Real.sinh (s.κ * s.a) ^ 2 :=
    mul_pos (pow_pos hσ 2) (pow_pos hs 2)
  linarith
lemma denominator_pos (s : Spectral) : 0 < absSq s.incidentAmplitude :=
  lt_trans (by norm_num) s.denominator_gt_one

lemma transmission_pos (s : Spectral) : 0 < s.transmission :=
  div_pos (by norm_num) s.denominator_pos
lemma transmission_lt_one (s : Spectral) : s.transmission < 1 := by
  unfold transmission
  exact (div_lt_one s.denominator_pos).2 s.denominator_gt_one

lemma reflection_add_transmission (s : Spectral) : s.reflection + s.transmission = 1 := by
  have h := s.amplitude_balance
  unfold reflection transmission
  -- Clear the common nonzero denominator only; conservation is proved from h.
  field_simp [ne_of_gt s.denominator_pos]
  <;> linarith

lemma reflection_pos (s : Spectral) : 0 < s.reflection := by
  have h := s.reflection_add_transmission
  have ht := s.transmission_lt_one
  linarith
lemma reflection_lt_one (s : Spectral) : s.reflection < 1 := by
  have h := s.reflection_add_transmission
  have ht := s.transmission_pos
  linarith

lemma transmission_closed (s : Spectral) :
    s.transmission = (1 + s.sigma ^ 2 * Real.sinh (s.κ * s.a) ^ 2)⁻¹ := by
  rw [transmission, s.incident_norm_formula, one_div]
lemma transmissionAmplitude_norm (s : Spectral) :
    absSq s.transmissionAmplitude = s.transmission := by
  simp only [transmissionAmplitude, transmission, absSq_div, absSq_one]
lemma reflectionAmplitude_norm (s : Spectral) :
    absSq s.reflectionAmplitude = s.reflection := by
  rw [reflectionAmplitude, absSq_div, reflection]

/-- Incident-current normalization is explicit and strictly nonzero. -/
lemma incident_flux_pos (s : Spectral) (hbar mass : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < (hbar / mass) * s.k * absSq s.incidentAmplitude := by
  exact mul_pos (mul_pos (div_pos hℏ hm) s.k_pos) s.denominator_pos

lemma transmitted_flux_ratio (s : Spectral) (hbar mass : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    ((hbar / mass) * s.k) /
      ((hbar / mass) * s.k * absSq s.incidentAmplitude) = s.transmission := by
  unfold transmission
  field_simp [ne_of_gt hℏ, ne_of_gt hm, ne_of_gt s.k_pos, ne_of_gt s.denominator_pos]
  <;> ring

lemma reflected_flux_ratio (s : Spectral) (hbar mass : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    -((hbar / mass) * (-s.k) * absSq s.reflectedAmplitude) /
      ((hbar / mass) * s.k * absSq s.incidentAmplitude) = s.reflection := by
  unfold reflection
  field_simp [ne_of_gt hℏ, ne_of_gt hm, ne_of_gt s.k_pos, ne_of_gt s.denominator_pos]
  <;> ring

end Spectral
end QuantumTunneling
