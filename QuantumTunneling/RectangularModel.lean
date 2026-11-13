/- Q4: one physical model for every positive incident energy.
Only physical data and positivity are inputs. The elementary propagation
profile is constructed, not hypothesized. Development source: uncompiled. -/
import QuantumTunneling.TransferUniqueness

noncomputable section
namespace QuantumTunneling

structure RectangularParameters where
  hbar : ℝ
  mass : ℝ
  energy : ℝ
  height : ℝ
  width : ℝ
  hbar_pos : 0 < hbar
  mass_pos : 0 < mass
  energy_pos : 0 < energy
  height_pos : 0 < height
  width_pos : 0 < width

namespace RectangularParameters

def k (p : RectangularParameters) : ℝ := Real.sqrt (2*p.mass*p.energy)/p.hbar
def q (p : RectangularParameters) : ℝ := Real.sqrt (2*p.mass*(p.energy-p.height))/p.hbar
def kappa (p : RectangularParameters) : ℝ := Real.sqrt (2*p.mass*(p.height-p.energy))/p.hbar
def kinetic (p : RectangularParameters) : ℝ := p.hbar^2/(2*p.mass)
def potential (p : RectangularParameters) (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ p.width then p.height else 0

lemma k_pos (p : RectangularParameters) : 0 < p.k := by
  exact div_pos (Real.sqrt_pos.2
    (mul_pos (mul_pos (by norm_num) p.mass_pos) p.energy_pos)) p.hbar_pos
lemma q_pos (p : RectangularParameters) (h : p.height<p.energy) : 0 < p.q := by
  exact div_pos (Real.sqrt_pos.2
    (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr h))) p.hbar_pos
lemma kappa_pos (p : RectangularParameters) (h : p.energy<p.height) : 0 < p.kappa := by
  exact div_pos (Real.sqrt_pos.2
    (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr h))) p.hbar_pos
lemma k_sq (p : RectangularParameters) : p.k^2=2*p.mass*p.energy/p.hbar^2 := by
  rw [k,div_pow,Real.sq_sqrt]
  exact le_of_lt (mul_pos (mul_pos (by norm_num) p.mass_pos) p.energy_pos)
lemma q_sq (p : RectangularParameters) (h : p.height<p.energy) :
    p.q^2=2*p.mass*(p.energy-p.height)/p.hbar^2 := by
  rw [q,div_pow,Real.sq_sqrt]
  exact le_of_lt (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr h))
lemma kappa_sq (p : RectangularParameters) (h : p.energy<p.height) :
    p.kappa^2=2*p.mass*(p.height-p.energy)/p.hbar^2 := by
  rw [kappa,div_pow,Real.sq_sqrt]
  exact le_of_lt (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr h))

/-- Trichotomy is used explicitly; neither strict branch is evaluated at E=V. -/
def profile (p : RectangularParameters) : PropagationProfile :=
  if hb : p.energy<p.height then PropagationProfile.evanescent p.kappa (p.kappa_pos hb)
  else if ha : p.height<p.energy then PropagationProfile.oscillatory p.q (p.q_pos ha)
  else PropagationProfile.critical

lemma profile_below (p : RectangularParameters) (h : p.energy<p.height) :
    p.profile=PropagationProfile.evanescent p.kappa (p.kappa_pos h) := by
  simp [profile,h]
lemma profile_above (p : RectangularParameters) (h : p.height<p.energy) :
    p.profile=PropagationProfile.oscillatory p.q (p.q_pos h) := by
  simp [profile,h,not_lt.mpr (le_of_lt h)]
lemma profile_critical (p : RectangularParameters) (h : p.energy=p.height) :
    p.profile=PropagationProfile.critical := by simp [profile,h]

/-- The signed interior spectral coefficient really equals 2m(E-V)/hbar². -/
lemma profile_delta (p : RectangularParameters) :
    p.profile.delta=2*p.mass*(p.energy-p.height)/p.hbar^2 := by
  rcases lt_trichotomy p.energy p.height with h | h | h
  · rw [p.profile_below h]
    change -(p.kappa^2)=_
    rw [p.kappa_sq h]
    ring
  · rw [p.profile_critical h]
    simp [PropagationProfile.critical,h]
  · rw [p.profile_above h]
    exact p.q_sq h

def layer (p : RectangularParameters) : ScatteringLayer :=
  ⟨p.k,p.width,p.k_pos,p.width_pos,p.profile⟩

def wave (p : RectangularParameters) : ℝ → ℂ := p.layer.normalizedWave
def waveD (p : RectangularParameters) : ℝ → ℂ := p.layer.normalizedD
def reflectionAmplitude (p : RectangularParameters) : ℂ := p.layer.reflectionAmplitude
def transmissionAmplitude (p : RectangularParameters) : ℂ := p.layer.transmissionAmplitude

lemma kinetic_k (p : RectangularParameters) : p.kinetic*p.k^2=p.energy := by
  rw [kinetic,p.k_sq]
  field_simp [ne_of_gt p.hbar_pos,ne_of_gt p.mass_pos] <;> ring
lemma kinetic_delta (p : RectangularParameters) :
    p.kinetic*p.profile.delta=p.energy-p.height := by
  rw [kinetic,p.profile_delta]
  field_simp [ne_of_gt p.hbar_pos,ne_of_gt p.mass_pos] <;> ring

lemma odeCoefficient_energy (p : RectangularParameters) (x : ℝ)
    (h0 : x ≠ 0) (ha : x ≠ p.width) :
    -p.kinetic*p.layer.odeCoefficient x+p.potential x=p.energy := by
  have hk := p.kinetic_k
  have hd := p.kinetic_delta
  by_cases hx : x<0
  · simp [ScatteringLayer.odeCoefficient,layer,potential,hx,not_le.mpr hx]
    nlinarith
  · have hxp : 0<x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm h0)
    by_cases hxa : x<p.width
    · simp [ScatteringLayer.odeCoefficient,layer,potential,hx,hxa,le_of_lt hxp,le_of_lt hxa]
      nlinarith
    · have hax : p.width<x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm ha)
      simp [ScatteringLayer.odeCoefficient,layer,potential,hx,hxa,not_le.mpr hax]
      nlinarith

/-- Literal real-space Schrödinger equation, with no interface C2 claim. -/
theorem schrodinger_wave (p : RectangularParameters) (x : ℝ)
    (h0 : x ≠ 0) (ha : x ≠ p.width) :
    (-(p.hbar^2/(2*p.mass)) : ℝ) • deriv (deriv p.wave) x+
      p.potential x • p.wave x=p.energy • p.wave x := by
  change (-p.kinetic : ℝ) • deriv (deriv p.layer.normalizedWave) x+
    p.potential x • p.layer.normalizedWave x=p.energy • p.layer.normalizedWave x
  rw [p.layer.second_deriv_normalized x h0 ha,smul_smul,← add_smul,
    p.odeCoefficient_energy x h0 ha]

/-- The universal contrast coefficient is nonsingular as E crosses V. -/
lemma beta_sq_physical (p : RectangularParameters) :
    p.layer.beta^2=p.mass*p.height^2/(2*p.hbar^2*p.energy) := by
  rw [ScatteringLayer.beta_sq]
  change (p.k^2-p.profile.delta)^2/(4*p.k^2)=_
  rw [p.k_sq,p.profile_delta]
  field_simp [ne_of_gt p.hbar_pos,ne_of_gt p.mass_pos,ne_of_gt p.energy_pos] <;> ring
lemma beta_ne_zero (p : RectangularParameters) : p.layer.beta ≠ 0 := by
  have hp : 0 < p.mass*p.height^2/(2*p.hbar^2*p.energy) := by
    exact div_pos (mul_pos p.mass_pos (pow_pos p.height_pos 2))
      (mul_pos (mul_pos (by norm_num) (pow_pos p.hbar_pos 2)) p.energy_pos)
  intro hz
  have hs := p.beta_sq_physical
  rw [hz] at hs
  norm_num at hs
  linarith

lemma inside_above (p : RectangularParameters) (h : p.height<p.energy) (x : ℝ) :
    p.layer.inside x=
      (⟨Real.cos (p.q*(x-p.width)), (p.k/p.q)*Real.sin (p.q*(x-p.width))⟩ : ℂ) := by
  apply Complex.ext <;>
    simp [ScatteringLayer.inside,layer,p.profile_above h,PropagationProfile.oscillatory] <;> ring
lemma inside_critical (p : RectangularParameters) (h : p.energy=p.height) (x : ℝ) :
    p.layer.inside x=(⟨1,p.k*(x-p.width)⟩ : ℂ) := by
  simp [ScatteringLayer.inside,layer,p.profile_critical h,PropagationProfile.critical]
lemma inside_below (p : RectangularParameters) (h : p.energy<p.height) (x : ℝ) :
    p.layer.inside x=
      (⟨Real.cosh (p.kappa*(x-p.width)), (p.k/p.kappa)*Real.sinh (p.kappa*(x-p.width))⟩ : ℂ) := by
  apply Complex.ext <;>
    simp [ScatteringLayer.inside,layer,p.profile_below h,PropagationProfile.evanescent] <;> ring

end RectangularParameters
end QuantumTunneling
