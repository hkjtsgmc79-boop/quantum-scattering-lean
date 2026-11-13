/- Q2: actual derivative and flux certificates for free waves. -/
import QuantumTunneling.ComplexTools

noncomputable section
namespace QuantumTunneling

def cis (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩
def plane (k x : ℝ) : ℂ := cis (k * x)
def planeD (k x : ℝ) : ℂ := ((k : ℂ) * Complex.I) * plane k x

@[simp] lemma cis_zero : cis 0 = 1 := by apply Complex.ext <;> simp [cis]
@[simp] lemma plane_zero (k : ℝ) : plane k 0 = 1 := by simp [plane]
lemma absSq_cis (θ : ℝ) : absSq (cis θ) = 1 := by
  simpa [absSq, cis, add_comm] using Real.sin_sq_add_cos_sq θ
lemma absSq_plane (k x : ℝ) : absSq (plane k x) = 1 := absSq_cis _
lemma cis_ne_zero (θ : ℝ) : cis θ ≠ 0 := by
  intro h
  have hh := absSq_cis θ
  rw [h, absSq_zero] at hh
  norm_num at hh

lemma hasDerivAt_plane (k x : ℝ) : HasDerivAt (plane k) (planeD k x) x := by
  have hp : HasDerivAt (fun s : ℝ => k * s) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have hd := hasDerivAt_mk hp.cos hp.sin
  convert hd using 1
  · rfl
  · apply Complex.ext <;> simp [plane, cis, planeD, Complex.mul_re, Complex.mul_im] <;> ring

lemma hasDerivAt_planeD (k x : ℝ) :
    HasDerivAt (planeD k) (-(k ^ 2 : ℝ) • plane k x) x := by
  have hd := (hasDerivAt_plane k x).const_mul ((k : ℂ) * Complex.I)
  convert hd using 1
  · rfl
  · apply Complex.ext <;> simp [planeD, Complex.real_smul, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

lemma second_deriv_plane (k x : ℝ) :
    deriv (deriv (plane k)) x = -(k ^ 2 : ℝ) • plane k x := by
  have h : deriv (plane k) = planeD k := funext fun y => (hasDerivAt_plane k y).deriv
  rw [h]
  exact (hasDerivAt_planeD k x).deriv

/-- Right-moving plus left-moving waves with unrestricted complex amplitudes. -/
def freeWave (k : ℝ) (A B : ℂ) (x : ℝ) : ℂ :=
  A * plane k x + B * plane (-k) x

def freeWaveD (k : ℝ) (A B : ℂ) (x : ℝ) : ℂ :=
  A * planeD k x + B * planeD (-k) x

lemma hasDerivAt_freeWave (k : ℝ) (A B : ℂ) (x : ℝ) :
    HasDerivAt (freeWave k A B) (freeWaveD k A B x) x := by
  exact ((hasDerivAt_plane k x).const_mul A).add
    ((hasDerivAt_plane (-k) x).const_mul B)

lemma hasDerivAt_freeWaveD (k : ℝ) (A B : ℂ) (x : ℝ) :
    HasDerivAt (freeWaveD k A B) (-(k ^ 2 : ℝ) • freeWave k A B x) x := by
  have hd := ((hasDerivAt_planeD k x).const_mul A).add
    ((hasDerivAt_planeD (-k) x).const_mul B)
  convert hd using 1
  · rfl
  · simp only [freeWave, Complex.real_smul, neg_sq, Complex.ofReal_neg, Complex.ofReal_pow]
    ring

/-- The interference terms cancel in the flux, not in the density. -/
lemma flux_freeWave (k : ℝ) (A B : ℂ) (x : ℝ) :
    fluxForm (freeWave k A B x) (freeWaveD k A B x) =
      k * (absSq A - absSq B) := by
  calc
    fluxForm (freeWave k A B x) (freeWaveD k A B x) =
        k * (absSq A - absSq B) *
          (Real.sin (k * x) ^ 2 + Real.cos (k * x) ^ 2) := by
      simp [fluxForm, freeWave, freeWaveD, planeD, plane, cis, absSq,
        Complex.mul_re, Complex.mul_im, neg_mul, Real.sin_neg, Real.cos_neg, -Real.sin_sq_add_cos_sq]
      <;> ring
    _ = k * (absSq A - absSq B) := by rw [Real.sin_sq_add_cos_sq, mul_one]

lemma flux_plane (k x : ℝ) : fluxForm (plane k x) (planeD k x) = k := by
  have h := flux_freeWave k 1 0 x
  simpa [freeWave, freeWaveD] using h

lemma current_freeWave (hbar mass k : ℝ) (A B : ℂ) (x : ℝ) :
    current hbar mass (freeWave k A B) x =
      (hbar / mass) * k * (absSq A - absSq B) := by
  rw [current, (hasDerivAt_freeWave k A B x).deriv, flux_freeWave]
  ring

end QuantumTunneling
