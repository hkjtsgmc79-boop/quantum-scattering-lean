/- Q4: explicit waves, actual first/second derivatives, and all four interfaces.
Development proof scripts, not yet compiled in this authoring environment. -/
import QuantumTunneling.TransferAmplitudes

noncomputable section
namespace QuantumTunneling
namespace ScatteringLayer

/-- Exit-normalized interior solution, valid also at delta = 0. -/
def inside (s : ScatteringLayer) (x : ℝ) : ℂ :=
  ⟨s.profile.C (x-s.a), s.k*s.profile.S (x-s.a)⟩
def insideD (s : ScatteringLayer) (x : ℝ) : ℂ :=
  ⟨-s.profile.delta*s.profile.S (x-s.a), s.k*s.profile.C (x-s.a)⟩
def right (s : ScatteringLayer) (x : ℝ) : ℂ := plane s.k (x-s.a)
def rightD (s : ScatteringLayer) (x : ℝ) : ℂ := planeD s.k (x-s.a)
def left (s : ScatteringLayer) : ℝ → ℂ := freeWave s.k s.A s.B
def leftD (s : ScatteringLayer) : ℝ → ℂ := freeWaveD s.k s.A s.B

lemma hasDerivAt_shiftC (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt (fun y => s.profile.C (y-s.a))
      (-s.profile.delta*s.profile.S (x-s.a)) x := by
  simpa [Function.comp_def] using (s.profile.C_deriv (x-s.a)).scomp x ((hasDerivAt_id x).sub_const s.a)
lemma hasDerivAt_shiftS (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt (fun y => s.profile.S (y-s.a)) (s.profile.C (x-s.a)) x := by
  simpa [Function.comp_def] using (s.profile.S_deriv (x-s.a)).scomp x ((hasDerivAt_id x).sub_const s.a)
lemma hasDerivAt_inside (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.inside (s.insideD x) x := by
  exact hasDerivAt_mk (s.hasDerivAt_shiftC x) ((s.hasDerivAt_shiftS x).const_mul s.k)
lemma hasDerivAt_insideD (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.insideD (-s.profile.delta • s.inside x) x := by
  have hd := hasDerivAt_mk
    ((s.hasDerivAt_shiftS x).const_mul (-s.profile.delta))
    ((s.hasDerivAt_shiftC x).const_mul s.k)
  convert hd using 1
  · rfl
  · apply Complex.ext <;>
    simp [insideD,inside,Complex.real_smul,Complex.mul_re,Complex.mul_im] <;> ring
lemma second_deriv_inside (s : ScatteringLayer) (x : ℝ) :
    deriv (deriv s.inside) x = -s.profile.delta • s.inside x := by
  have hd : deriv s.inside=s.insideD := funext fun y => (s.hasDerivAt_inside y).deriv
  rw [hd]
  exact (s.hasDerivAt_insideD x).deriv

lemma hasDerivAt_right (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.right (s.rightD x) x := by
  change HasDerivAt (fun t => plane s.k (t-s.a)) _ x
  simpa [right, rightD, Function.comp_def] using
    (hasDerivAt_plane s.k (x-s.a)).scomp x ((hasDerivAt_id x).sub_const s.a)
lemma hasDerivAt_rightD (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.rightD (-(s.k^2 : ℝ) • s.right x) x := by
  change HasDerivAt (fun t => planeD s.k (t-s.a)) _ x
  simpa [right, rightD, Function.comp_def] using
    (hasDerivAt_planeD s.k (x-s.a)).scomp x ((hasDerivAt_id x).sub_const s.a)
lemma hasDerivAt_left (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.left (s.leftD x) x := hasDerivAt_freeWave _ _ _ _
lemma hasDerivAt_leftD (s : ScatteringLayer) (x : ℝ) :
    HasDerivAt s.leftD (-(s.k^2 : ℝ) • s.left x) x := hasDerivAt_freeWaveD _ _ _ _

@[simp] lemma inside_at_exit (s : ScatteringLayer) : s.inside s.a=1 := by
  apply Complex.ext <;> simp [inside,s.profile.C_zero,s.profile.S_zero]
@[simp] lemma right_at_exit (s : ScatteringLayer) : s.right s.a=1 := by simp [right]
lemma insideD_at_exit (s : ScatteringLayer) : s.insideD s.a=(s.k : ℂ)*Complex.I := by
  apply Complex.ext <;> simp [insideD,s.profile.C_zero,s.profile.S_zero]
lemma rightD_at_exit (s : ScatteringLayer) : s.rightD s.a=(s.k : ℂ)*Complex.I := by
  simp [rightD,planeD]
lemma match_right_value (s : ScatteringLayer) : s.inside s.a=s.right s.a := by simp
lemma match_right_derivative (s : ScatteringLayer) : s.insideD s.a=s.rightD s.a := by
  rw [s.insideD_at_exit,s.rightD_at_exit]
lemma match_left_value (s : ScatteringLayer) : s.left 0=s.inside 0 := by
  apply Complex.ext <;>
    simp [left,freeWave,A,B,inside,alpha,beta,s.profile.C_neg,s.profile.S_neg]
    <;> field_simp [ne_of_gt s.k_pos] <;> ring
lemma match_left_derivative (s : ScatteringLayer) : s.leftD 0=s.insideD 0 := by
  apply Complex.ext <;>
    simp [leftD,freeWaveD,planeD,A,B,insideD,alpha,beta,s.profile.C_neg,s.profile.S_neg,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_neg]
    <;> field_simp [ne_of_gt s.k_pos] <;> ring

lemma flux_inside (s : ScatteringLayer) (x : ℝ) :
    fluxForm (s.inside x) (s.insideD x)=s.k := by
  calc
    fluxForm (s.inside x) (s.insideD x)=s.k*
      ((s.profile.C (x-s.a))^2+s.profile.delta*(s.profile.S (x-s.a))^2) := by
        simp only [fluxForm,inside,insideD]
        ring
    _=s.k := by rw [s.profile.invariant,mul_one]
lemma flux_right (s : ScatteringLayer) (x : ℝ) :
    fluxForm (s.right x) (s.rightD x)=s.k := flux_plane _ _
lemma flux_left (s : ScatteringLayer) (x : ℝ) :
    fluxForm (s.left x) (s.leftD x)=s.k := by
  rw [left,leftD,flux_freeWave,s.amplitude_balance,mul_one]

end ScatteringLayer
end QuantumTunneling
