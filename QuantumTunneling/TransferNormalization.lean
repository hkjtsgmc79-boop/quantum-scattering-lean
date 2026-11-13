/- Q4 development module: nonzero normalization and genuine global C1. -/
import QuantumTunneling.TransferGluing

noncomputable section
namespace QuantumTunneling
namespace ScatteringLayer

def normalizedWave (s : ScatteringLayer) (x : ℝ) : ℂ := s.wave x / s.A
def normalizedD (s : ScatteringLayer) (x : ℝ) : ℂ := s.waveD x / s.A

lemma hasDerivAt_normalized (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.normalizedWave (s.normalizedD x) x := by
  change HasDerivAt (fun t => s.wave t / s.A) (s.normalizedD x) x
  simpa only [normalizedD, div_eq_mul_inv] using
    (s.hasDerivAt_wave x).mul_const s.A⁻¹

lemma deriv_normalized (s : ScatteringLayer) : deriv s.normalizedWave = s.normalizedD :=
  funext fun x => (s.hasDerivAt_normalized x).deriv

lemma hasDerivAt_normalizedD (s : ScatteringLayer) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    HasDerivAt s.normalizedD (s.odeCoefficient x • s.normalizedWave x) x := by
  have hd := (s.hasDerivAt_waveD x h0 ha).mul_const s.A⁻¹
  convert hd using 1
  · funext t
    simp only [normalizedD, div_eq_mul_inv]
  · simp only [normalizedWave, div_eq_mul_inv, Complex.real_smul]
    ring

lemma second_deriv_normalized (s : ScatteringLayer) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    deriv (deriv s.normalizedWave) x = s.odeCoefficient x • s.normalizedWave x := by
  rw [s.deriv_normalized]
  exact (s.hasDerivAt_normalizedD x h0 ha).deriv

lemma normalized_left (s : ScatteringLayer) (x : ℝ) (hx : x < 0) :
    s.normalizedWave x = plane s.k x + s.reflectionAmplitude * plane (-s.k) x := by
  simp only [normalizedWave, wave, join, if_pos hx, left, freeWave, reflectionAmplitude]
  field_simp [s.A_ne_zero]
  <;> ring

lemma normalized_right (s : ScatteringLayer) (x : ℝ) (hx : s.a < x) :
    s.normalizedWave x = s.transmissionAmplitude * plane s.k (x - s.a) := by
  have hx0 : ¬x < 0 := not_lt.mpr (le_of_lt (lt_trans s.a_pos hx))
  have hxa : ¬x < s.a := not_lt.mpr (le_of_lt hx)
  simp only [normalizedWave, wave, tail, join, if_neg hx0, if_neg hxa,
    right, transmissionAmplitude]
  ring

lemma normalized_inside (s : ScatteringLayer) (x : ℝ) (h0 : 0 ≤ x) (ha : x ≤ s.a) :
    s.normalizedWave x = s.inside x / s.A := by
  have hx0 : ¬x < 0 := not_lt.mpr h0
  by_cases hxa : x < s.a
  · simp [normalizedWave, wave, tail, join, hx0, hxa]
  · have heq : x = s.a := le_antisymm ha (le_of_not_gt hxa)
    subst x
    simp [normalizedWave, wave, tail, join, not_lt.mpr (le_of_lt s.a_pos)]

lemma current_normalized (s : ScatteringLayer) (hbar mass x : ℝ) :
    current hbar mass s.normalizedWave x =
      (hbar / mass) * s.k * s.T := by
  rw [current, s.deriv_normalized]
  change (hbar / mass) * fluxForm (s.wave x / s.A)
    (s.waveD x / s.A) = _
  rw [fluxForm_div]
  have hflux : fluxForm (s.wave x) (s.waveD x) = s.k := by
    simpa only [s.deriv_wave] using s.flux_wave x
  rw [hflux, s.T_as_inv]
  ring

/-- Positive net current exists on both sides AND inside the barrier. -/
lemma current_normalized_pos (s : ScatteringLayer) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < current hbar mass s.normalizedWave x := by
  rw [s.current_normalized]
  exact mul_pos (mul_pos (div_pos hℏ hm) s.k_pos) s.T_pos


lemma continuous_leftD (s : ScatteringLayer) : Continuous s.leftD :=
  (show Differentiable ℝ s.leftD from fun x => (s.hasDerivAt_leftD x).differentiableAt).continuous
lemma continuous_insideD (s : ScatteringLayer) : Continuous s.insideD :=
  (show Differentiable ℝ s.insideD from fun x => (s.hasDerivAt_insideD x).differentiableAt).continuous
lemma continuous_rightD (s : ScatteringLayer) : Continuous s.rightD :=
  (show Differentiable ℝ s.rightD from fun x => (s.hasDerivAt_rightD x).differentiableAt).continuous
lemma continuous_tailD (s : ScatteringLayer) : Continuous s.tailD :=
  continuous_join s.a s.insideD s.rightD s.continuous_insideD s.continuous_rightD
    s.match_right_derivative
lemma continuous_waveD (s : ScatteringLayer) : Continuous s.waveD := by
  apply continuous_join 0 s.leftD s.tailD s.continuous_leftD s.continuous_tailD
  simpa [tailD,join,s.a_pos] using s.match_left_derivative
lemma differentiable_normalizedWave (s : ScatteringLayer) : Differentiable ℝ s.normalizedWave :=
  fun x => (s.hasDerivAt_normalized x).differentiableAt
lemma continuous_normalizedD (s : ScatteringLayer) : Continuous s.normalizedD := by
  change Continuous (fun t => s.waveD t / s.A)
  simpa only [normalizedD,div_eq_mul_inv] using s.continuous_waveD.mul_const s.A⁻¹
/-- Actual global C1 regularity, including both interfaces. -/
theorem contDiff_one_normalizedWave (s : ScatteringLayer) :
    ContDiff ℝ 1 s.normalizedWave := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨s.differentiable_normalizedWave, ?_⟩
  rw [s.deriv_normalized]
  exact s.continuous_normalizedD

end ScatteringLayer
end QuantumTunneling
