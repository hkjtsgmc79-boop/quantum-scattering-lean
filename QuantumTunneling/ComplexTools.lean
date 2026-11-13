/- Q2: see README for exact verification status. -/
import QuantumTunneling.Basic

noncomputable section
namespace QuantumTunneling

/-- Squared complex modulus, in coordinates for robust algebraic normalization. -/
def absSq (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

/-- Imaginary part of conjugate(z) * w. The actual current uses w = deriv ψ. -/
def fluxForm (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

lemma absSq_eq_normSq (z : ℂ) : absSq z = Complex.normSq z := by
  simp [absSq, Complex.normSq_apply, pow_two]
lemma absSq_eq_norm_sq (z : ℂ) : absSq z = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, absSq_eq_normSq]
lemma absSq_nonneg (z : ℂ) : 0 ≤ absSq z := by
  unfold absSq
  positivity
@[simp] lemma absSq_zero : absSq (0 : ℂ) = 0 := by simp [absSq]
@[simp] lemma absSq_one : absSq (1 : ℂ) = 1 := by norm_num [absSq]
lemma absSq_mul (z w : ℂ) : absSq (z * w) = absSq z * absSq w := by
  simp only [absSq, Complex.mul_re, Complex.mul_im]
  ring
lemma absSq_ne_zero {z : ℂ} (hz : z ≠ 0) : absSq z ≠ 0 := by
  rw [absSq_eq_norm_sq]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
lemma absSq_div (z w : ℂ) : absSq (z / w) = absSq z / absSq w := by
  simp only [absSq_eq_norm_sq, norm_div, div_pow]
lemma fluxForm_eq_im (z w : ℂ) :
    fluxForm z w = (star z * w).im := by
  simp [fluxForm, Complex.mul_im]
  ring
lemma fluxForm_scale (c z w : ℂ) :
    fluxForm (c * z) (c * w) = absSq c * fluxForm z w := by
  simp only [fluxForm, absSq, Complex.mul_re, Complex.mul_im]
  ring
lemma fluxForm_div (z w c : ℂ) :
    fluxForm (z / c) (w / c) = fluxForm z w / absSq c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [mul_comm z c⁻¹, mul_comm w c⁻¹, fluxForm_scale]
  have hc : absSq c⁻¹ = (absSq c)⁻¹ := by
    simpa using absSq_div 1 c
  rw [hc]
  ring

/-- The real derivative of a complex function is assembled without using complex
holomorphic differentiation in the physical space coordinate. -/
lemma hasDerivAt_mk {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => (⟨f s, g s⟩ : ℂ)) (⟨f', g'⟩ : ℂ) x := by
  have hd := hf.ofReal_comp.add (hg.ofReal_comp.mul_const Complex.I)
  change HasDerivAt (fun s => (f s : ℂ) + (g s : ℂ) * Complex.I)
    ((f' : ℂ) + (g' : ℂ) * Complex.I) x at hd
  simpa only [← Complex.mk_eq_add_mul_I] using hd

/-- Probability current for a stationary (not L²-normalized) scattering state. -/
def current (hbar mass : ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  (hbar / mass) * fluxForm (ψ x) (deriv ψ x)

lemma current_eq_conjugate (hbar mass : ℝ) (ψ : ℝ → ℂ) (x : ℝ) :
    current hbar mass ψ x = (hbar / mass) * (star (ψ x) * deriv ψ x).im := by
  rw [current, fluxForm_eq_im]

end QuantumTunneling
