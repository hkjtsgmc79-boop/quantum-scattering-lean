/- Q2: exact two-interface matching and incoming/outgoing amplitudes. -/
import QuantumTunneling.BarrierWave

noncomputable section
namespace QuantumTunneling
namespace Spectral

def delta (s : Spectral) : ℝ := (s.κ / s.k - s.k / s.κ) / 2
def sigma (s : Spectral) : ℝ := (s.κ / s.k + s.k / s.κ) / 2

def incidentAmplitude (s : Spectral) : ℂ :=
  ⟨Real.cosh (s.κ * s.a), s.delta * Real.sinh (s.κ * s.a)⟩
def reflectedAmplitude (s : Spectral) : ℂ :=
  ⟨0, -s.sigma * Real.sinh (s.κ * s.a)⟩

def left (s : Spectral) : ℝ → ℂ := freeWave s.k s.incidentAmplitude s.reflectedAmplitude
def leftD (s : Spectral) : ℝ → ℂ := freeWaveD s.k s.incidentAmplitude s.reflectedAmplitude

lemma sigma_pos (s : Spectral) : 0 < s.sigma := by
  exact div_pos (add_pos (div_pos s.κ_pos s.k_pos) (div_pos s.k_pos s.κ_pos))
    (by norm_num)
lemma sigma_sq_sub_delta_sq (s : Spectral) : s.sigma ^ 2 - s.delta ^ 2 = 1 := by
  unfold sigma delta
  field_simp [ne_of_gt s.k_pos, ne_of_gt s.κ_pos]
  <;> ring
lemma sigma_sq (s : Spectral) :
    s.sigma ^ 2 = (s.k ^ 2 + s.κ ^ 2) ^ 2 / (4 * s.k ^ 2 * s.κ ^ 2) := by
  unfold sigma
  field_simp [ne_of_gt s.k_pos, ne_of_gt s.κ_pos]
  <;> ring

lemma hasDerivAt_left (s : Spectral) (x : ℝ) : HasDerivAt s.left (s.leftD x) x :=
  hasDerivAt_freeWave _ _ _ _
lemma hasDerivAt_leftD (s : Spectral) (x : ℝ) :
    HasDerivAt s.leftD (-(s.k ^ 2 : ℝ) • s.left x) x :=
  hasDerivAt_freeWaveD _ _ _ _
lemma second_deriv_left (s : Spectral) (x : ℝ) :
    deriv (deriv s.left) x = -(s.k ^ 2 : ℝ) • s.left x := by
  have h : deriv s.left = s.leftD := funext fun y => (s.hasDerivAt_left y).deriv
  rw [h]
  exact (s.hasDerivAt_leftD x).deriv

/-- At x=0, the sum A+B matches the interior value, including its phase. -/
lemma match_left_value (s : Spectral) : s.left 0 = s.inside 0 := by
  apply Complex.ext <;>
    simp [left, freeWave, incidentAmplitude, reflectedAmplitude, inside, delta, sigma,
      mul_neg, Real.cosh_neg, Real.sinh_neg]
  <;> field_simp [ne_of_gt s.k_pos, ne_of_gt s.κ_pos] <;> ring

/-- At x=0, ik(A-B) matches the derivative, with the reflected sign reversed. -/
lemma match_left_derivative (s : Spectral) : s.leftD 0 = s.insideD 0 := by
  apply Complex.ext <;>
    simp [leftD, freeWaveD, planeD, incidentAmplitude, reflectedAmplitude,
      insideD, delta, sigma, Complex.mul_re, Complex.mul_im, mul_neg,
      Real.cosh_neg, Real.sinh_neg]
  <;> field_simp [ne_of_gt s.k_pos, ne_of_gt s.κ_pos] <;> ring

lemma match_right_value (s : Spectral) : s.inside s.a = s.right s.a := by simp
lemma match_right_derivative (s : Spectral) : s.insideD s.a = s.rightD s.a := by
  rw [insideD_at_exit, rightD_at_exit]

lemma absSq_reflected (s : Spectral) :
    absSq s.reflectedAmplitude = s.sigma ^ 2 * Real.sinh (s.κ * s.a) ^ 2 := by
  simp [absSq, reflectedAmplitude]
  ring

/-- Wronskian/flux balance derived from the matched amplitudes. -/
lemma amplitude_balance (s : Spectral) :
    absSq s.incidentAmplitude - absSq s.reflectedAmplitude = 1 := by
  have h₁ : s.delta ^ 2 + 1 - s.sigma ^ 2 = 0 := by
    linarith [s.sigma_sq_sub_delta_sq]
  calc
    absSq s.incidentAmplitude - absSq s.reflectedAmplitude =
        (Real.cosh (s.κ * s.a) ^ 2 - Real.sinh (s.κ * s.a) ^ 2) +
        (s.delta ^ 2 + 1 - s.sigma ^ 2) * Real.sinh (s.κ * s.a) ^ 2 := by
      simp only [absSq, incidentAmplitude, reflectedAmplitude]
      ring
    _ = 1 := by rw [h₁, Real.cosh_sq_sub_sinh_sq]; ring

lemma incident_norm_formula (s : Spectral) :
    absSq s.incidentAmplitude = 1 + s.sigma ^ 2 * Real.sinh (s.κ * s.a) ^ 2 := by
  have h := s.amplitude_balance
  rw [s.absSq_reflected] at h
  linarith

lemma incident_ne_zero (s : Spectral) : s.incidentAmplitude ≠ 0 := by
  intro h
  have hb := s.amplitude_balance
  have hn := absSq_nonneg s.reflectedAmplitude
  rw [h, absSq_zero] at hb
  linarith

lemma flux_left (s : Spectral) (x : ℝ) :
    fluxForm (s.left x) (s.leftD x) = s.k := by
  rw [left, leftD, flux_freeWave, s.amplitude_balance, mul_one]

end Spectral
end QuantumTunneling
