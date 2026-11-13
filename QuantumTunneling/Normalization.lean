/- Q2: incident amplitude one, obtained by a justified nonzero division. -/
import QuantumTunneling.Physical

noncomputable section
namespace QuantumTunneling
namespace Spectral

def normalizedWave (s : Spectral) (x : ℝ) : ℂ := s.wave x / s.incidentAmplitude
def normalizedD (s : Spectral) (x : ℝ) : ℂ := s.waveD x / s.incidentAmplitude

lemma hasDerivAt_normalized (s : Spectral) (x : ℝ) :
    HasDerivAt s.normalizedWave (s.normalizedD x) x := by
  change HasDerivAt (fun t => s.wave t / s.incidentAmplitude) (s.normalizedD x) x
  simpa only [normalizedD, div_eq_mul_inv] using
    (s.hasDerivAt_wave x).mul_const s.incidentAmplitude⁻¹

lemma deriv_normalized (s : Spectral) : deriv s.normalizedWave = s.normalizedD :=
  funext fun x => (s.hasDerivAt_normalized x).deriv

lemma hasDerivAt_normalizedD (s : Spectral) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    HasDerivAt s.normalizedD (s.odeCoefficient x • s.normalizedWave x) x := by
  have hd := (s.hasDerivAt_waveD x h0 ha).mul_const s.incidentAmplitude⁻¹
  convert hd using 1
  · funext t
    simp only [normalizedD, div_eq_mul_inv]
  · simp only [normalizedWave, div_eq_mul_inv, Complex.real_smul]
    ring

lemma second_deriv_normalized (s : Spectral) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    deriv (deriv s.normalizedWave) x = s.odeCoefficient x • s.normalizedWave x := by
  rw [s.deriv_normalized]
  exact (s.hasDerivAt_normalizedD x h0 ha).deriv

lemma normalized_left (s : Spectral) (x : ℝ) (hx : x < 0) :
    s.normalizedWave x = plane s.k x + s.reflectionAmplitude * plane (-s.k) x := by
  simp only [normalizedWave, wave, join, if_pos hx, left, freeWave, reflectionAmplitude]
  field_simp [s.incident_ne_zero]
  <;> ring

lemma normalized_right (s : Spectral) (x : ℝ) (hx : s.a < x) :
    s.normalizedWave x = s.transmissionAmplitude * plane s.k (x - s.a) := by
  have hx0 : ¬x < 0 := not_lt.mpr (le_of_lt (lt_trans s.a_pos hx))
  have hxa : ¬x < s.a := not_lt.mpr (le_of_lt hx)
  simp only [normalizedWave, wave, tail, join, if_neg hx0, if_neg hxa,
    right, transmissionAmplitude]
  ring

lemma normalized_inside (s : Spectral) (x : ℝ) (h0 : 0 ≤ x) (ha : x ≤ s.a) :
    s.normalizedWave x = s.inside x / s.incidentAmplitude := by
  have hx0 : ¬x < 0 := not_lt.mpr h0
  by_cases hxa : x < s.a
  · simp [normalizedWave, wave, tail, join, hx0, hxa]
  · have heq : x = s.a := le_antisymm ha (le_of_not_gt hxa)
    subst x
    simp [normalizedWave, wave, tail, join, not_lt.mpr (le_of_lt s.a_pos)]

lemma current_normalized (s : Spectral) (hbar mass x : ℝ) :
    current hbar mass s.normalizedWave x =
      (hbar / mass) * s.k * s.transmission := by
  rw [current, s.deriv_normalized]
  change (hbar / mass) * fluxForm (s.wave x / s.incidentAmplitude)
    (s.waveD x / s.incidentAmplitude) = _
  rw [fluxForm_div]
  have hflux : fluxForm (s.wave x) (s.waveD x) = s.k := by
    simpa only [s.deriv_wave] using s.flux_wave x
  rw [hflux, transmission]
  ring

/-- Positive net current exists on both sides AND inside the barrier. -/
lemma current_normalized_pos (s : Spectral) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < current hbar mass s.normalizedWave x := by
  rw [s.current_normalized]
  exact mul_pos (mul_pos (div_pos hℏ hm) s.k_pos) s.transmission_pos

end Spectral
namespace Parameters

lemma schrodinger_normalized (p : Parameters) (x : ℝ)
    (h0 : x ≠ 0) (ha : x ≠ p.width) :
    (-(p.hbar ^ 2 / (2 * p.mass)) : ℝ) • deriv (deriv p.spectral.normalizedWave) x +
      p.potential x • p.spectral.normalizedWave x = p.energy • p.spectral.normalizedWave x := by
  rw [p.spectral.second_deriv_normalized x h0 ha, smul_smul, ← add_smul,
    p.odeCoefficient_energy x h0 ha]

end Parameters
end QuantumTunneling
