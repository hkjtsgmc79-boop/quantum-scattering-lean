/-
Q2: continuous first derivative across both finite-potential interfaces.
This module proves global C¹ regularity of the actual glued wave. It makes no
claim of a global second derivative at either discontinuity of the potential.
Checked with Lean 4.30.0 and the fixed project Mathlib revision.
-/
import QuantumTunneling.Normalization
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered

noncomputable section
open Set
namespace QuantumTunneling

/-- Pasting continuous formulas at a point needs equality of their values.
Applied to the first-derivative formulas below, this is precisely the second
matching condition at each interface; differentiability alone is not used to
infer continuity of a derivative. -/
lemma continuous_join (c : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (heq : f c = g c) :
    Continuous (join c f g) := by
  change Continuous (fun x : ℝ => if x < c then f x else g x)
  apply continuous_if
  · intro x hx
    change x ∈ frontier (Iio c) at hx
    have hxc : x = c := by
      simpa only [frontier_Iio, mem_singleton_iff] using hx
    simpa only [hxc] using heq
  · exact hf.continuousOn
  · exact hg.continuousOn

namespace Spectral

/-- The left derivative formula is smooth on the full line independently of
the final piecewise assembly. Its second-derivative certificate implies this
continuity without differentiating across a potential jump. -/
lemma continuous_leftD (s : Spectral) : Continuous s.leftD := by
  have hd : Differentiable ℝ s.leftD :=
    fun x => (s.hasDerivAt_leftD x).differentiableAt
  exact hd.continuous

lemma continuous_insideD (s : Spectral) : Continuous s.insideD := by
  have hd : Differentiable ℝ s.insideD :=
    fun x => (s.hasDerivAt_insideD x).differentiableAt
  exact hd.continuous

lemma continuous_rightD (s : Spectral) : Continuous s.rightD := by
  have hd : Differentiable ℝ s.rightD :=
    fun x => (s.hasDerivAt_rightD x).differentiableAt
  exact hd.continuous

lemma continuous_tailD (s : Spectral) : Continuous s.tailD := by
  exact continuous_join s.a s.insideD s.rightD
    s.continuous_insideD s.continuous_rightD s.match_right_derivative

/-- Both boundary matching equations are used: first the exit, then the entry. -/
lemma continuous_waveD (s : Spectral) : Continuous s.waveD := by
  apply continuous_join 0 s.leftD s.tailD s.continuous_leftD s.continuous_tailD
  simpa [tailD, join, s.a_pos] using s.match_left_derivative

/-- Continuity concerns the actual derivative selected by Lean's `deriv`. -/
theorem continuous_deriv_wave (s : Spectral) : Continuous (deriv s.wave) := by
  rw [s.deriv_wave]
  exact s.continuous_waveD

theorem contDiff_one_wave (s : Spectral) : ContDiff ℝ 1 s.wave := by
  exact contDiff_one_iff_deriv.mpr
    ⟨s.differentiable_wave, s.continuous_deriv_wave⟩

lemma differentiable_normalizedWave (s : Spectral) :
    Differentiable ℝ s.normalizedWave :=
  fun x => (s.hasDerivAt_normalized x).differentiableAt

lemma continuous_normalizedWave (s : Spectral) : Continuous s.normalizedWave :=
  s.differentiable_normalizedWave.continuous

lemma continuous_normalizedD (s : Spectral) : Continuous s.normalizedD := by
  change Continuous (fun t => s.waveD t / s.incidentAmplitude)
  simpa only [normalizedD, div_eq_mul_inv] using
    s.continuous_waveD.mul_const s.incidentAmplitude⁻¹

/-- The unit-incident scattering wave has a continuous derivative everywhere,
including both potential interfaces. -/
theorem continuous_deriv_normalizedWave (s : Spectral) :
    Continuous (deriv s.normalizedWave) := by
  rw [s.deriv_normalized]
  exact s.continuous_normalizedD

theorem contDiff_one_normalizedWave (s : Spectral) :
    ContDiff ℝ 1 s.normalizedWave := by
  exact contDiff_one_iff_deriv.mpr
    ⟨s.differentiable_normalizedWave, s.continuous_deriv_normalizedWave⟩

/-- At the entry the actual derivative equals the interior trace. -/
lemma deriv_wave_at_entry (s : Spectral) : deriv s.wave 0 = s.insideD 0 := by
  rw [s.deriv_wave]
  simp [waveD, tailD, join, s.a_pos]

/-- At the exit the actual derivative agrees with the transmitted wave. -/
lemma deriv_wave_at_exit (s : Spectral) :
    deriv s.wave s.a = (s.k : ℂ) * Complex.I := by
  rw [s.deriv_wave]
  simp [waveD, tailD, join, not_lt.mpr (le_of_lt s.a_pos), s.rightD_at_exit]

lemma deriv_normalized_at_entry (s : Spectral) :
    deriv s.normalizedWave 0 = s.insideD 0 / s.incidentAmplitude := by
  rw [s.deriv_normalized]
  simp [normalizedD, waveD, tailD, join, s.a_pos]

lemma deriv_normalized_at_exit (s : Spectral) :
    deriv s.normalizedWave s.a =
      ((s.k : ℂ) * Complex.I) / s.incidentAmplitude := by
  rw [s.deriv_normalized]
  simp [normalizedD, waveD, tailD, join,
    not_lt.mpr (le_of_lt s.a_pos), s.rightD_at_exit]

end Spectral
namespace Parameters

/-- The physical parameters produce the same globally C¹ scattering wave;
no new regularity condition is added to the physical input structure. -/
theorem scatteringWave_C1 (p : Parameters) :
    ContDiff ℝ 1 p.spectral.normalizedWave :=
  p.spectral.contDiff_one_normalizedWave

end Parameters
end QuantumTunneling
