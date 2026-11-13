/- Q4: the Q2 pasting argument applied to the full signed interior spectrum.
New module is a development candidate; Q2 original files remain unchanged. -/
import QuantumTunneling.TransferWaves

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumTunneling
namespace ScatteringLayer

def tail (s : ScatteringLayer) : ℝ → ℂ := join s.a s.inside s.right
def tailD (s : ScatteringLayer) : ℝ → ℂ := join s.a s.insideD s.rightD
/-- A single physical-space function, not three unrelated local solutions. -/
def wave (s : ScatteringLayer) : ℝ → ℂ := join 0 s.left s.tail
def waveD (s : ScatteringLayer) : ℝ → ℂ := join 0 s.leftD s.tailD

def odeCoefficient (s : ScatteringLayer) (x : ℝ) : ℝ :=
  if x < 0 then -(s.k ^ 2) else if x < s.a then -s.profile.delta else -(s.k ^ 2)

lemma hasDerivAt_tail (s : ScatteringLayer) (x : ℝ) : HasDerivAt s.tail (s.tailD x) x :=
  hasDerivAt_join s.a s.inside s.insideD s.right s.rightD
    s.hasDerivAt_inside s.hasDerivAt_right s.match_right_value s.match_right_derivative x

lemma hasDerivAt_wave (s : ScatteringLayer) (x : ℝ) : HasDerivAt s.wave (s.waveD x) x := by
  apply hasDerivAt_join 0 s.left s.leftD s.tail s.tailD
    s.hasDerivAt_left s.hasDerivAt_tail
  · simpa [tail, join, s.a_pos] using s.match_left_value
  · simpa [tailD, join, s.a_pos] using s.match_left_derivative

lemma deriv_wave (s : ScatteringLayer) : deriv s.wave = s.waveD :=
  funext fun x => (s.hasDerivAt_wave x).deriv
lemma differentiable_wave (s : ScatteringLayer) : Differentiable ℝ s.wave :=
  fun x => (s.hasDerivAt_wave x).differentiableAt
lemma continuous_wave (s : ScatteringLayer) : Continuous s.wave := s.differentiable_wave.continuous

lemma hasDerivAt_waveD (s : ScatteringLayer) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    HasDerivAt s.waveD (s.odeCoefficient x • s.wave x) x := by
  by_cases hx : x < 0
  · simp only [odeCoefficient, wave, join, if_pos hx]
    apply (s.hasDerivAt_leftD x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    change y < 0 at hy
    simp [waveD, join, hy]
  · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm h0)
    by_cases hxa : x < s.a
    · simp only [odeCoefficient, wave, tail, join, if_neg hx, if_pos hxa]
      apply (s.hasDerivAt_insideD x).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hxpos, isOpen_Iio.mem_nhds hxa] with y hy0 hya
      change 0 < y at hy0
      change y < s.a at hya
      simp [waveD, tailD, join, not_lt.mpr (le_of_lt hy0), hya]
    · have hax : s.a < x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm ha)
      simp only [odeCoefficient, wave, tail, join, if_neg hx, if_neg hxa]
      apply (s.hasDerivAt_rightD x).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hax] with y hy
      change s.a < y at hy
      have hy0 : 0 < y := lt_trans s.a_pos hy
      simp [waveD, tailD, join, not_lt.mpr (le_of_lt hy0), not_lt.mpr (le_of_lt hy)]

lemma second_deriv_wave (s : ScatteringLayer) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    deriv (deriv s.wave) x = s.odeCoefficient x • s.wave x := by
  rw [s.deriv_wave]
  exact (s.hasDerivAt_waveD x h0 ha).deriv

lemma flux_wave (s : ScatteringLayer) (x : ℝ) :
    fluxForm (s.wave x) (deriv s.wave x) = s.k := by
  rw [s.deriv_wave]
  by_cases h0 : x < 0
  · simpa [wave, waveD, join, h0] using s.flux_left x
  · by_cases ha : x < s.a
    · simpa [wave, waveD, tail, tailD, join, h0, ha] using s.flux_inside x
    · simpa [wave, waveD, tail, tailD, join, h0, ha] using s.flux_right x

lemma current_wave (s : ScatteringLayer) (hbar mass x : ℝ) :
    current hbar mass s.wave x = (hbar / mass) * s.k := by
  rw [current, s.flux_wave]

end ScatteringLayer
end QuantumTunneling
