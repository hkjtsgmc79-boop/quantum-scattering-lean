/- Q4 development source; no new kernel verification is claimed. -/
import QuantumTunneling.PropagationProfile

noncomputable section
namespace QuantumTunneling
namespace ScatteringLayer

/-- These coefficients remain finite at the threshold delta = 0. -/
def alpha (s : ScatteringLayer) : ℝ := (s.k^2 + s.profile.delta)/(2*s.k)
def beta (s : ScatteringLayer) : ℝ := (s.profile.delta - s.k^2)/(2*s.k)
def A (s : ScatteringLayer) : ℂ := ⟨s.profile.C s.a, -s.alpha*s.profile.S s.a⟩
def B (s : ScatteringLayer) : ℂ := ⟨0, s.beta*s.profile.S s.a⟩

lemma alpha_sub_beta (s : ScatteringLayer) : s.alpha-s.beta=s.k := by
  unfold alpha beta
  field_simp [ne_of_gt s.k_pos] <;> ring
lemma alpha_add_beta (s : ScatteringLayer) : s.alpha+s.beta=s.profile.delta/s.k := by
  unfold alpha beta
  field_simp [ne_of_gt s.k_pos] <;> ring
lemma alpha_sq_sub_beta_sq (s : ScatteringLayer) :
    s.alpha^2-s.beta^2=s.profile.delta := by
  unfold alpha beta
  field_simp [ne_of_gt s.k_pos] <;> ring
lemma beta_sq (s : ScatteringLayer) :
    s.beta^2=(s.k^2-s.profile.delta)^2/(4*s.k^2) := by
  unfold beta
  field_simp [ne_of_gt s.k_pos] <;> ring

lemma absSq_B (s : ScatteringLayer) : absSq s.B=s.beta^2*(s.profile.S s.a)^2 := by
  simp only [B, absSq]
  ring
lemma amplitude_balance (s : ScatteringLayer) : absSq s.A-absSq s.B=1 := by
  calc
    absSq s.A-absSq s.B = (s.profile.C s.a)^2 +
        (s.alpha^2-s.beta^2)*(s.profile.S s.a)^2 := by
      simp only [A,B,absSq]
      ring
    _ = 1 := by rw [s.alpha_sq_sub_beta_sq]; exact s.profile.invariant s.a
lemma absSq_A (s : ScatteringLayer) : absSq s.A=1+s.beta^2*(s.profile.S s.a)^2 := by
  have h := s.amplitude_balance
  rw [s.absSq_B] at h
  linarith
lemma A_ne_zero (s : ScatteringLayer) : s.A ≠ 0 := by
  intro hz
  have hb := s.amplitude_balance
  rw [hz, absSq_zero] at hb
  have hn := absSq_nonneg s.B
  linarith

/-- Unit-incident complex amplitudes, obtained by nonzero normalization. -/
def reflectionAmplitude (s : ScatteringLayer) : ℂ := s.B/s.A
def transmissionAmplitude (s : ScatteringLayer) : ℂ := 1/s.A
def R (s : ScatteringLayer) : ℝ := absSq s.reflectionAmplitude
def T (s : ScatteringLayer) : ℝ := absSq s.transmissionAmplitude

lemma T_as_inv (s : ScatteringLayer) : s.T=(absSq s.A)⁻¹ := by
  unfold T transmissionAmplitude
  rw [absSq_div, absSq_one, one_div]
lemma T_formula (s : ScatteringLayer) : s.T=(1+s.beta^2*(s.profile.S s.a)^2)⁻¹ := by
  rw [s.T_as_inv,s.absSq_A]
lemma R_add_T (s : ScatteringLayer) : s.R+s.T=1 := by
  rw [R,T,reflectionAmplitude,transmissionAmplitude,absSq_div,absSq_div,absSq_one]
  have hA := s.amplitude_balance
  have hne := absSq_ne_zero s.A_ne_zero
  field_simp [hne]
  linarith
lemma R_nonneg (s : ScatteringLayer) : 0 ≤ s.R := absSq_nonneg _
lemma T_pos (s : ScatteringLayer) : 0 < s.T := by
  rw [s.T_formula]
  exact inv_pos.2 (by positivity)
lemma T_le_one (s : ScatteringLayer) : s.T ≤ 1 := by
  have h := s.R_add_T
  have hR := s.R_nonneg
  linarith
lemma R_lt_one (s : ScatteringLayer) : s.R < 1 := by
  have h := s.R_add_T
  have hT := s.T_pos
  linarith

/-- This criterion will become sin(qa)=0 above the barrier. -/
lemma T_eq_one_iff (s : ScatteringLayer) :
    s.T=1 ↔ s.beta*s.profile.S s.a=0 := by
  have hden : 0 < 1+s.beta^2*(s.profile.S s.a)^2 := by positivity
  rw [s.T_formula]
  constructor
  · intro h
    have hi : (1+s.beta^2*(s.profile.S s.a)^2) *
        (1+s.beta^2*(s.profile.S s.a)^2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hden)
    rw [h, mul_one] at hi
    have hz : s.beta^2*(s.profile.S s.a)^2=0 := by linarith
    have hs : (s.beta*s.profile.S s.a)^2=0 := by rw [mul_pow,hz]
    exact sq_eq_zero_iff.mp hs
  · intro h
    have hz : s.beta^2*(s.profile.S s.a)^2=0 := by
      rw [← mul_pow,h]
      norm_num
    rw [hz]
    norm_num
lemma R_eq_zero_iff (s : ScatteringLayer) : s.R=0 ↔ s.T=1 := by
  have h := s.R_add_T
  constructor <;> intro hz <;> linarith
lemma T_lt_one_of_nonresonant (s : ScatteringLayer) (h : s.beta*s.profile.S s.a ≠ 0) :
    s.T<1 := by
  exact lt_of_le_of_ne s.T_le_one (fun ht => h ((s.T_eq_one_iff).1 ht))

end ScatteringLayer
end QuantumTunneling
