/- Q2: uniqueness of left plane-wave coefficients at fixed exit normalization.
This does not assert a general spectral theorem or Hilbert-space scattering completeness. -/
import QuantumTunneling.Matching

noncomputable section
namespace QuantumTunneling

lemma freeWave_at_zero (k : ℝ) (A B : ℂ) : freeWave k A B 0 = A + B := by
  simp [freeWave]
lemma freeWaveD_at_zero (k : ℝ) (A B : ℂ) :
    freeWaveD k A B 0 = ((k : ℂ) * Complex.I) * (A - B) := by
  simp [freeWaveD, planeD, Complex.ofReal_neg]
  ring

lemma free_coefficients_unique (k : ℝ) (hk : k ≠ 0) (A B C D : ℂ)
    (hv : freeWave k A B 0 = freeWave k C D 0)
    (hd : freeWaveD k A B 0 = freeWaveD k C D 0) : A = C ∧ B = D := by
  rw [freeWave_at_zero, freeWave_at_zero] at hv
  rw [freeWaveD_at_zero, freeWaveD_at_zero] at hd
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hki : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero hkC Complex.I_ne_zero
  have hs : A - B = C - D := mul_left_cancel₀ hki hd
  constructor
  · linear_combination (1 / 2 : ℂ) * hv + (1 / 2 : ℂ) * hs
  · linear_combination (1 / 2 : ℂ) * hv - (1 / 2 : ℂ) * hs

namespace Spectral
lemma matched_left_coefficients_unique (s : Spectral) (A B : ℂ)
    (hv : freeWave s.k A B 0 = s.inside 0)
    (hd : freeWaveD s.k A B 0 = s.insideD 0) :
    A = s.incidentAmplitude ∧ B = s.reflectedAmplitude := by
  apply free_coefficients_unique s.k (ne_of_gt s.k_pos) A B s.incidentAmplitude s.reflectedAmplitude
  · exact hv.trans s.match_left_value.symm
  · exact hd.trans s.match_left_derivative.symm
end Spectral
end QuantumTunneling
