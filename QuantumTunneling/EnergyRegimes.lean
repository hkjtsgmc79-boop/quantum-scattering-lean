/- Q4: the three exact transmission formulas, including the omitted threshold.
These are consequences of a matched global C1 wave and its actual current.
Development source: requires a fresh Lean build. -/
import QuantumTunneling.RectangularModel

noncomputable section
namespace QuantumTunneling
namespace RectangularParameters

lemma S_below (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.profile.S p.layer.a=Real.sinh (p.kappa*p.width)/p.kappa := by
  simp [layer,p.profile_below h,PropagationProfile.evanescent]
lemma S_above (p : RectangularParameters) (h : p.height<p.energy) :
    p.layer.profile.S p.layer.a=Real.sin (p.q*p.width)/p.q := by
  simp [layer,p.profile_above h,PropagationProfile.oscillatory]
lemma S_critical (p : RectangularParameters) (h : p.energy=p.height) :
    p.layer.profile.S p.layer.a=p.width := by
  simp [layer,p.profile_critical h,PropagationProfile.critical]

lemma contrast_below (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.beta^2/p.kappa^2=p.height^2/(4*p.energy*(p.height-p.energy)) := by
  rw [p.beta_sq_physical,p.kappa_sq h]
  field_simp [ne_of_gt p.mass_pos,ne_of_gt p.hbar_pos,ne_of_gt p.energy_pos,
    ne_of_gt (sub_pos.mpr h)] <;> ring
lemma contrast_above (p : RectangularParameters) (h : p.height<p.energy) :
    p.layer.beta^2/p.q^2=p.height^2/(4*p.energy*(p.energy-p.height)) := by
  rw [p.beta_sq_physical,p.q_sq h]
  field_simp [ne_of_gt p.mass_pos,ne_of_gt p.hbar_pos,ne_of_gt p.energy_pos,
    ne_of_gt (sub_pos.mpr h)] <;> ring

theorem transmission_below (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.T=(1+p.height^2/(4*p.energy*(p.height-p.energy))*
      Real.sinh (p.kappa*p.width)^2)⁻¹ := by
  rw [p.layer.T_formula,p.S_below h,div_pow]
  have hc := p.contrast_below h
  calc
    (1+p.layer.beta^2*(Real.sinh (p.kappa*p.width)^2/p.kappa^2))⁻¹ =
      (1+(p.layer.beta^2/p.kappa^2)*Real.sinh (p.kappa*p.width)^2)⁻¹ := by
        congr 1
        ring
    _=_ := by rw [hc]

theorem transmission_above (p : RectangularParameters) (h : p.height<p.energy) :
    p.layer.T=(1+p.height^2/(4*p.energy*(p.energy-p.height))*
      Real.sin (p.q*p.width)^2)⁻¹ := by
  rw [p.layer.T_formula,p.S_above h,div_pow]
  have hc := p.contrast_above h
  calc
    (1+p.layer.beta^2*(Real.sin (p.q*p.width)^2/p.q^2))⁻¹ =
      (1+(p.layer.beta^2/p.q^2)*Real.sin (p.q*p.width)^2)⁻¹ := by
        congr 1
        ring
    _=_ := by rw [hc]

/-- At E=V the interior wave is linear. No limiting argument or 0/0 is used. -/
theorem transmission_critical (p : RectangularParameters) (h : p.energy=p.height) :
    p.layer.T=(1+p.mass*p.height*p.width^2/(2*p.hbar^2))⁻¹ := by
  have hb : p.layer.beta^2=p.mass*p.height/(2*p.hbar^2) := by
    rw [p.beta_sq_physical,h]
    field_simp [ne_of_gt p.height_pos,ne_of_gt p.hbar_pos] <;> ring
  rw [p.layer.T_formula,p.S_critical h,hb]
  congr 1
  ring

lemma transmission_below_lt_one (p : RectangularParameters) (h : p.energy<p.height) :
    p.layer.T<1 := by
  apply p.layer.T_lt_one_of_nonresonant
  apply mul_ne_zero p.beta_ne_zero
  rw [p.S_below h]
  exact ne_of_gt (div_pos
    (Real.sinh_pos_iff.2 (mul_pos (p.kappa_pos h) p.width_pos)) (p.kappa_pos h))
lemma transmission_critical_lt_one (p : RectangularParameters) (h : p.energy=p.height) :
    p.layer.T<1 := by
  apply p.layer.T_lt_one_of_nonresonant
  rw [p.S_critical h]
  exact mul_ne_zero p.beta_ne_zero (ne_of_gt p.width_pos)

/-- For a genuine positive barrier, perfect transmission is exactly resonance. -/
theorem above_resonance_iff (p : RectangularParameters) (h : p.height<p.energy) :
    p.layer.T=1 ↔ Real.sin (p.q*p.width)=0 := by
  rw [p.layer.T_eq_one_iff,p.S_above h]
  constructor
  · intro hz
    have hs : Real.sin (p.q*p.width)/p.q=0 :=
      (mul_eq_zero.mp hz).resolve_left p.beta_ne_zero
    exact (div_eq_zero_iff.mp hs).resolve_right (ne_of_gt (p.q_pos h))
  · intro hz
    rw [hz,zero_div,mul_zero]

theorem above_resonance_reflection (p : RectangularParameters) (h : p.height<p.energy) :
    p.layer.R=0 ↔ Real.sin (p.q*p.width)=0 := by
  rw [p.layer.R_eq_zero_iff,p.above_resonance_iff h]

/-- The combined result is a genuine three-way cover, not only two open regions. -/
theorem all_energy_transmission_cases (p : RectangularParameters) :
    (p.energy<p.height → p.layer.T=(1+p.height^2/(4*p.energy*(p.height-p.energy))*
      Real.sinh (p.kappa*p.width)^2)⁻¹) ∧
    (p.height<p.energy → p.layer.T=(1+p.height^2/(4*p.energy*(p.energy-p.height))*
      Real.sin (p.q*p.width)^2)⁻¹) ∧
    (p.energy=p.height → p.layer.T=(1+p.mass*p.height*p.width^2/(2*p.hbar^2))⁻¹) :=
  ⟨p.transmission_below,p.transmission_above,p.transmission_critical⟩

end RectangularParameters
end QuantumTunneling
