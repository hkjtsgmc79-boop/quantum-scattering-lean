/- Q2: explicit evanescent solution, anchored at the exit x = a. -/
import QuantumTunneling.PlaneWave

noncomputable section
namespace QuantumTunneling
namespace Spectral

/-- Exit normalization ψ(a)=1. Both growing and decaying exponentials are present. -/
def inside (s : Spectral) (x : ℝ) : ℂ :=
  ⟨Real.cosh (s.κ * (x - s.a)),
   (s.k / s.κ) * Real.sinh (s.κ * (x - s.a))⟩

def insideD (s : Spectral) (x : ℝ) : ℂ :=
  ⟨s.κ * Real.sinh (s.κ * (x - s.a)),
   s.k * Real.cosh (s.κ * (x - s.a))⟩

def right (s : Spectral) (x : ℝ) : ℂ := plane s.k (x - s.a)
def rightD (s : Spectral) (x : ℝ) : ℂ := planeD s.k (x - s.a)

lemma hasDerivAt_inside (s : Spectral) (x : ℝ) :
    HasDerivAt s.inside (s.insideD x) x := by
  have hp : HasDerivAt (fun y : ℝ => s.κ * (y - s.a)) s.κ x := by
    simpa using ((hasDerivAt_id x).sub_const s.a).const_mul s.κ
  have hd := hasDerivAt_mk hp.cosh (hp.sinh.const_mul (s.k / s.κ))
  convert hd using 1
  · rfl
  · apply Complex.ext <;> simp [inside, insideD] <;>
    field_simp [ne_of_gt s.κ_pos] <;> ring

lemma hasDerivAt_insideD (s : Spectral) (x : ℝ) :
    HasDerivAt s.insideD (s.κ ^ 2 • s.inside x) x := by
  have hp : HasDerivAt (fun y : ℝ => s.κ * (y - s.a)) s.κ x := by
    simpa using ((hasDerivAt_id x).sub_const s.a).const_mul s.κ
  have hd := hasDerivAt_mk (hp.sinh.const_mul s.κ) (hp.cosh.const_mul s.k)
  convert hd using 1
  · rfl
  · apply Complex.ext <;> simp [inside, insideD, Complex.real_smul, pow_two, Complex.mul_re, Complex.mul_im] <;>
    field_simp [ne_of_gt s.κ_pos] <;> ring

lemma second_deriv_inside (s : Spectral) (x : ℝ) :
    deriv (deriv s.inside) x = s.κ ^ 2 • s.inside x := by
  have h : deriv s.inside = s.insideD := funext fun y => (s.hasDerivAt_inside y).deriv
  rw [h]
  exact (s.hasDerivAt_insideD x).deriv

lemma hasDerivAt_right (s : Spectral) (x : ℝ) :
    HasDerivAt s.right (s.rightD x) x := by
  change HasDerivAt (fun t => plane s.k (t - s.a)) _ x
  simpa [right, rightD, Function.comp_def] using
    (hasDerivAt_plane s.k (x - s.a)).scomp x ((hasDerivAt_id x).sub_const s.a)

lemma hasDerivAt_rightD (s : Spectral) (x : ℝ) :
    HasDerivAt s.rightD (-(s.k ^ 2 : ℝ) • s.right x) x := by
  change HasDerivAt (fun t => planeD s.k (t - s.a)) _ x
  simpa [right, rightD, Function.comp_def] using
    (hasDerivAt_planeD s.k (x - s.a)).scomp x ((hasDerivAt_id x).sub_const s.a)

lemma second_deriv_right (s : Spectral) (x : ℝ) :
    deriv (deriv s.right) x = -(s.k ^ 2 : ℝ) • s.right x := by
  have h : deriv s.right = s.rightD := funext fun y => (s.hasDerivAt_right y).deriv
  rw [h]
  exact (s.hasDerivAt_rightD x).deriv

@[simp] lemma inside_at_exit (s : Spectral) : s.inside s.a = 1 := by
  apply Complex.ext <;> simp [inside]
@[simp] lemma right_at_exit (s : Spectral) : s.right s.a = 1 := by
  simp [right]
lemma insideD_at_exit (s : Spectral) : s.insideD s.a = (s.k : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [insideD]
lemma rightD_at_exit (s : Spectral) : s.rightD s.a = (s.k : ℂ) * Complex.I := by
  simp [rightD, planeD]

lemma flux_inside (s : Spectral) (x : ℝ) :
    fluxForm (s.inside x) (s.insideD x) = s.k := by
  calc
    fluxForm (s.inside x) (s.insideD x) = s.k *
        (Real.cosh (s.κ * (x - s.a)) ^ 2 -
         Real.sinh (s.κ * (x - s.a)) ^ 2) := by
      simp only [fluxForm, inside, insideD]
      field_simp [ne_of_gt s.κ_pos]
      <;> ring
    _ = s.k := by rw [Real.cosh_sq_sub_sinh_sq, mul_one]

lemma flux_right (s : Spectral) (x : ℝ) :
    fluxForm (s.right x) (s.rightD x) = s.k := flux_plane _ _

end Spectral
end QuantumTunneling
