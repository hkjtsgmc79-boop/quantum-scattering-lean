/- Q4: all four matching coefficients, including the linear threshold basis.
Uniqueness is within the stated elementary scattering ansatz, not a spectral
completeness claim. All derivatives below are actual `deriv` values. -/
import QuantumTunneling.TransferObservables

noncomputable section
namespace QuantumTunneling
namespace ScatteringLayer

def combination (s : ScatteringLayer) (c d : ℂ) (x : ℝ) : ℂ :=
  c*(s.profile.C (x-s.a) : ℂ)+d*(s.profile.S (x-s.a) : ℂ)
def combinationD (s : ScatteringLayer) (c d : ℂ) (x : ℝ) : ℂ :=
  c*((-s.profile.delta*s.profile.S (x-s.a) : ℝ) : ℂ)+d*(s.profile.C (x-s.a) : ℂ)
def exitSlope (s : ScatteringLayer) : ℂ := (s.k : ℂ)*Complex.I

lemma hasDerivAt_combination (s : ScatteringLayer) (c d : ℂ) (x : ℝ) :
    HasDerivAt (s.combination c d) (s.combinationD c d x) x := by
  exact ((s.hasDerivAt_shiftC x).ofReal_comp.const_mul c).add
    ((s.hasDerivAt_shiftS x).ofReal_comp.const_mul d)
lemma deriv_combination (s : ScatteringLayer) (c d : ℂ) (x : ℝ) :
    deriv (s.combination c d) x=s.combinationD c d x :=
  (s.hasDerivAt_combination c d x).deriv
@[simp] lemma combination_exit (s : ScatteringLayer) (c d : ℂ) :
    s.combination c d s.a=c := by simp [combination,s.profile.C_zero,s.profile.S_zero]
@[simp] lemma combinationD_exit (s : ScatteringLayer) (c d : ℂ) :
    s.combinationD c d s.a=d := by simp [combinationD,s.profile.C_zero,s.profile.S_zero]
lemma combination_scaled (s : ScatteringLayer) (t : ℂ) (x : ℝ) :
    s.combination t (t*s.exitSlope) x=t*s.inside x := by
  apply Complex.ext <;>
    simp [combination,exitSlope,inside,Complex.mul_re,Complex.mul_im] <;> ring
lemma combinationD_scaled (s : ScatteringLayer) (t : ℂ) (x : ℝ) :
    s.combinationD t (t*s.exitSlope) x=t*s.insideD x := by
  apply Complex.ext <;>
    simp [combinationD,exitSlope,insideD,Complex.mul_re,Complex.mul_im] <;> ring

structure BoundaryMatched (s : ScatteringLayer) (r t c d : ℂ) : Prop where
  left_value : freeWave s.k 1 r 0=s.combination c d 0
  left_derivative : deriv (freeWave s.k 1 r) 0=deriv (s.combination c d) 0
  right_value : s.combination c d s.a=t*s.right s.a
  right_derivative : deriv (s.combination c d) s.a=deriv (fun x=>t*s.right x) s.a

lemma boundaryMatched_exit (s : ScatteringLayer) (r t c d : ℂ)
    (h : s.BoundaryMatched r t c d) : c=t ∧ d=t*s.exitSlope := by
  have hc : c=t := by simpa using h.right_value
  have hd := h.right_derivative
  rw [s.deriv_combination,s.combinationD_exit,
    ((s.hasDerivAt_right s.a).const_mul t).deriv,s.rightD_at_exit] at hd
  exact ⟨hc,hd⟩
lemma freeWave_scaled (s : ScatteringLayer) (t : ℂ) (x : ℝ) :
    freeWave s.k (t*s.A) (t*s.B) x=t*s.left x := by
  simp only [left,freeWave]
  ring
lemma freeWaveD_scaled (s : ScatteringLayer) (t : ℂ) (x : ℝ) :
    freeWaveD s.k (t*s.A) (t*s.B) x=t*s.leftD x := by
  simp only [leftD,freeWaveD]
  ring

theorem boundaryMatched_unique (s : ScatteringLayer) (r t c d : ℂ)
    (h : s.BoundaryMatched r t c d) :
    r=s.reflectionAmplitude ∧ t=s.transmissionAmplitude ∧
      c=s.transmissionAmplitude ∧ d=s.transmissionAmplitude*s.exitSlope := by
  obtain ⟨hc,hd⟩ := s.boundaryMatched_exit r t c d h
  have hv := h.left_value
  rw [hc,hd,s.combination_scaled] at hv
  have hder := h.left_derivative
  rw [(hasDerivAt_freeWave s.k 1 r 0).deriv,s.deriv_combination,
    hc,hd,s.combinationD_scaled] at hder
  have hv' : freeWave s.k 1 r 0=freeWave s.k (t*s.A) (t*s.B) 0 := by
    rw [s.freeWave_scaled,s.match_left_value]
    exact hv
  have hd' : freeWaveD s.k 1 r 0=freeWaveD s.k (t*s.A) (t*s.B) 0 := by
    rw [s.freeWaveD_scaled,s.match_left_derivative]
    exact hder
  obtain ⟨hA,hB⟩ := free_coefficients_unique s.k (ne_of_gt s.k_pos)
    1 r (t*s.A) (t*s.B) hv' hd'
  have ht : t=s.transmissionAmplitude := (eq_div_iff s.A_ne_zero).2 hA.symm
  have hr : r=s.reflectionAmplitude := by
    rw [hB,ht]
    unfold transmissionAmplitude reflectionAmplitude
    ring
  exact ⟨hr,ht,hc.trans ht,hd.trans (congrArg (fun z=>z*s.exitSlope) ht)⟩

lemma normalized_freeWave (s : ScatteringLayer) (x : ℝ) :
    freeWave s.k 1 s.reflectionAmplitude x=s.transmissionAmplitude*s.left x := by
  simp only [left,freeWave,reflectionAmplitude,transmissionAmplitude]
  field_simp [s.A_ne_zero] <;> ring
lemma normalized_freeWaveD (s : ScatteringLayer) (x : ℝ) :
    freeWaveD s.k 1 s.reflectionAmplitude x=s.transmissionAmplitude*s.leftD x := by
  simp only [leftD,freeWaveD,reflectionAmplitude,transmissionAmplitude]
  field_simp [s.A_ne_zero] <;> ring

theorem canonical_boundaryMatched (s : ScatteringLayer) :
    s.BoundaryMatched s.reflectionAmplitude s.transmissionAmplitude
      s.transmissionAmplitude (s.transmissionAmplitude*s.exitSlope) := by
  constructor
  · rw [s.normalized_freeWave,s.combination_scaled,s.match_left_value]
  · rw [(hasDerivAt_freeWave s.k 1 s.reflectionAmplitude 0).deriv,
      s.deriv_combination,s.normalized_freeWaveD,s.combinationD_scaled,s.match_left_derivative]
  · rw [s.combination_scaled,s.match_right_value]
  · rw [s.deriv_combination,s.combinationD_scaled,
      ((s.hasDerivAt_right s.a).const_mul s.transmissionAmplitude).deriv,s.match_right_derivative]

theorem boundaryMatched_iff (s : ScatteringLayer) (r t c d : ℂ) :
    s.BoundaryMatched r t c d ↔
      r=s.reflectionAmplitude ∧ t=s.transmissionAmplitude ∧
      c=s.transmissionAmplitude ∧ d=s.transmissionAmplitude*s.exitSlope := by
  constructor
  · exact s.boundaryMatched_unique r t c d
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    exact s.canonical_boundaryMatched

end ScatteringLayer
end QuantumTunneling
