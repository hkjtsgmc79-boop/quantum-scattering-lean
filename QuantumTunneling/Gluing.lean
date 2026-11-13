/- Q2: genuine global first derivative and second derivative off interfaces.
Checked with Lean 4.30.0 and the fixed project Mathlib revision.
At a finite jump in potential we do NOT claim global twice differentiability. -/
import QuantumTunneling.Matching

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumTunneling

/-- Glue two globally smooth formulas along one interface. -/
def join (c : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ := if x < c then f x else g x

lemma hasDerivAt_join_boundary (c : ℝ) (f g : ℝ → ℂ) (d : ℂ)
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (heq : f c = g c) :
    HasDerivAt (join c f g) d c := by
  have hl : HasDerivWithinAt (join c f g) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx
      change x ≤ c at hx
      by_cases hxc : x < c
      · simp [join, hxc]
      · have hxc' : x = c := le_antisymm hx (le_of_not_gt hxc)
        subst x
        simpa [join] using heq.symm
    · simpa [join] using heq.symm
  have hr : HasDerivWithinAt (join c f g) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro x hx
      change c ≤ x at hx
      simp [join, not_lt.mpr hx]
    · simp [join]
  have hu : Iic c ∪ Ici c = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x c
  have h := hl.union hr
  rw [hu] at h
  exact h.hasDerivAt (by simp)

lemma hasDerivAt_join (c : ℝ) (f fD g gD : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (fD x) x) (hg : ∀ x, HasDerivAt g (gD x) x)
    (hval : f c = g c) (hder : fD c = gD c) (x : ℝ) :
    HasDerivAt (join c f g) (join c fD gD x) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · rw [join, if_pos hx]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    change y < c at hy
    simp [join, hy]
  · subst x
    have hf' : HasDerivAt f (gD c) c := (hf c).congr_deriv hder
    simpa [join] using hasDerivAt_join_boundary c f g (gD c) hf' (hg c) hval
  · rw [join, if_neg (not_lt.mpr (le_of_lt hx))]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    change c < y at hy
    simp [join, not_lt.mpr (le_of_lt hy)]

namespace Spectral

def tail (s : Spectral) : ℝ → ℂ := join s.a s.inside s.right
def tailD (s : Spectral) : ℝ → ℂ := join s.a s.insideD s.rightD
/-- A single physical-space function, not three unrelated local solutions. -/
def wave (s : Spectral) : ℝ → ℂ := join 0 s.left s.tail
def waveD (s : Spectral) : ℝ → ℂ := join 0 s.leftD s.tailD

def odeCoefficient (s : Spectral) (x : ℝ) : ℝ :=
  if x < 0 then -(s.k ^ 2) else if x < s.a then s.κ ^ 2 else -(s.k ^ 2)

lemma hasDerivAt_tail (s : Spectral) (x : ℝ) : HasDerivAt s.tail (s.tailD x) x :=
  hasDerivAt_join s.a s.inside s.insideD s.right s.rightD
    s.hasDerivAt_inside s.hasDerivAt_right s.match_right_value s.match_right_derivative x

lemma hasDerivAt_wave (s : Spectral) (x : ℝ) : HasDerivAt s.wave (s.waveD x) x := by
  apply hasDerivAt_join 0 s.left s.leftD s.tail s.tailD
    s.hasDerivAt_left s.hasDerivAt_tail
  · simpa [tail, join, s.a_pos] using s.match_left_value
  · simpa [tailD, join, s.a_pos] using s.match_left_derivative

lemma deriv_wave (s : Spectral) : deriv s.wave = s.waveD :=
  funext fun x => (s.hasDerivAt_wave x).deriv
lemma differentiable_wave (s : Spectral) : Differentiable ℝ s.wave :=
  fun x => (s.hasDerivAt_wave x).differentiableAt
lemma continuous_wave (s : Spectral) : Continuous s.wave := s.differentiable_wave.continuous

lemma hasDerivAt_waveD (s : Spectral) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
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

lemma second_deriv_wave (s : Spectral) (x : ℝ) (h0 : x ≠ 0) (ha : x ≠ s.a) :
    deriv (deriv s.wave) x = s.odeCoefficient x • s.wave x := by
  rw [s.deriv_wave]
  exact (s.hasDerivAt_waveD x h0 ha).deriv

lemma flux_wave (s : Spectral) (x : ℝ) :
    fluxForm (s.wave x) (deriv s.wave x) = s.k := by
  rw [s.deriv_wave]
  by_cases h0 : x < 0
  · simpa [wave, waveD, join, h0] using s.flux_left x
  · by_cases ha : x < s.a
    · simpa [wave, waveD, tail, tailD, join, h0, ha] using s.flux_inside x
    · simpa [wave, waveD, tail, tailD, join, h0, ha] using s.flux_right x

lemma current_wave (s : Spectral) (hbar mass x : ℝ) :
    current hbar mass s.wave x = (hbar / mass) * s.k := by
  rw [current, s.flux_wave]

end Spectral
end QuantumTunneling
