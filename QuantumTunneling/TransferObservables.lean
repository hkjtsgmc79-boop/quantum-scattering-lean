/- Q4: actual current ratios in every energy regime. Development source.
Equal exterior wave numbers and a common mass are explicit model choices. -/
import QuantumTunneling.TransferNormalization

noncomputable section
namespace QuantumTunneling
namespace ScatteringLayer
lemma reflectionAmplitude_norm (s : ScatteringLayer) : absSq s.reflectionAmplitude=s.R := rfl
lemma transmissionAmplitude_norm (s : ScatteringLayer) : absSq s.transmissionAmplitude=s.T := rfl


/-- The unit-amplitude incoming component on the left. -/
def incidentComponent (s : ScatteringLayer) : ℝ → ℂ := freeWave s.k 1 0

/-- The outgoing reflected component on the left, with negative wave number. -/
def reflectedComponent (s : ScatteringLayer) : ℝ → ℂ :=
  freeWave s.k 0 s.reflectionAmplitude

/-- The outgoing transmitted component, with its phase anchored at the exit. -/
def transmittedComponent (s : ScatteringLayer) (x : ℝ) : ℂ :=
  s.transmissionAmplitude * s.right x

lemma normalized_left_components (s : ScatteringLayer) (x : ℝ) (hx : x < 0) :
    s.normalizedWave x = s.incidentComponent x + s.reflectedComponent x := by
  simpa only [incidentComponent, reflectedComponent, freeWave,
    one_mul, zero_mul, add_zero, zero_add] using s.normalized_left x hx

lemma normalized_right_component (s : ScatteringLayer) (x : ℝ) (hx : s.a < x) :
    s.normalizedWave x = s.transmittedComponent x := by
  exact s.normalized_right x hx

/-- The incoming-from-the-right coefficient is explicitly zero. -/
lemma normalized_right_outgoing_only (s : ScatteringLayer) (x : ℝ) (hx : s.a < x) :
    s.normalizedWave x = freeWave s.k s.transmissionAmplitude 0 (x - s.a) := by
  simpa only [freeWave, zero_mul, add_zero] using s.normalized_right x hx

/-- The unit incident flux, computed using the actual derivative. -/
lemma current_incidentComponent (s : ScatteringLayer) (hbar mass x : ℝ) :
    current hbar mass s.incidentComponent x = (hbar / mass) * s.k := by
  simp only [incidentComponent, current_freeWave, absSq_one, absSq_zero,
    sub_zero, mul_one]

/-- Reflected current is signed: it points toward decreasing x. -/
lemma current_reflectedComponent (s : ScatteringLayer) (hbar mass x : ℝ) :
    current hbar mass s.reflectedComponent x =
      -((hbar / mass) * s.k * s.R) := by
  rw [reflectedComponent, current_freeWave, absSq_zero, s.reflectionAmplitude_norm]
  ring

/-- The exit component uses the derivative of the shifted plane wave. -/
lemma current_transmittedComponent (s : ScatteringLayer) (hbar mass x : ℝ) :
    current hbar mass s.transmittedComponent x =
      (hbar / mass) * s.k * s.T := by
  have hd := (s.hasDerivAt_right x).const_mul s.transmissionAmplitude
  change (hbar / mass) * fluxForm (s.transmissionAmplitude * s.right x)
    (deriv (fun y => s.transmissionAmplitude * s.right y) x) = _
  rw [hd.deriv, fluxForm_scale, s.flux_right, s.transmissionAmplitude_norm]
  ring

lemma current_incidentComponent_pos (s : ScatteringLayer) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < current hbar mass s.incidentComponent x := by
  rw [s.current_incidentComponent]
  exact mul_pos (div_pos hℏ hm) s.k_pos

/-- Above-barrier resonances may have zero reflected current. -/
lemma current_reflectedComponent_nonpos (s : ScatteringLayer) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    current hbar mass s.reflectedComponent x ≤ 0 := by
  rw [s.current_reflectedComponent]
  have h : 0 ≤ (hbar/mass)*s.k*s.R :=
    mul_nonneg (le_of_lt (mul_pos (div_pos hℏ hm) s.k_pos)) s.R_nonneg
  linarith

lemma current_transmittedComponent_pos (s : ScatteringLayer) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < current hbar mass s.transmittedComponent x := by
  rw [s.current_transmittedComponent]
  exact mul_pos (mul_pos (div_pos hℏ hm) s.k_pos) s.T_pos

/-- The physical transmitted/incident current ratio is exactly T. The sample
points may differ because each component current is spatially constant. -/
theorem transmission_eq_current_ratio (s : ScatteringLayer) (hbar mass xL xR : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    current hbar mass s.transmittedComponent xR /
      current hbar mass s.incidentComponent xL = s.T := by
  rw [s.current_transmittedComponent, s.current_incidentComponent]
  have hfactor : (hbar / mass) * s.k ≠ 0 :=
    ne_of_gt (mul_pos (div_pos hℏ hm) s.k_pos)
  apply (div_eq_iff hfactor).2
  ring

/-- Reflection is the magnitude of the negative reflected current divided by
the positive incident current. The minus sign is essential. -/
theorem reflection_eq_current_ratio (s : ScatteringLayer) (hbar mass xI xR : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    -(current hbar mass s.reflectedComponent xR) /
      current hbar mass s.incidentComponent xI = s.R := by
  rw [s.current_reflectedComponent, s.current_incidentComponent]
  have hfactor : (hbar / mass) * s.k ≠ 0 :=
    ne_of_gt (mul_pos (div_pos hℏ hm) s.k_pos)
  apply (div_eq_iff hfactor).2
  ring

/-- Net left current equals transmitted current; reflected current is signed. -/
theorem component_current_balance (s : ScatteringLayer) (hbar mass xL xR : ℝ) :
    current hbar mass s.incidentComponent xL +
        current hbar mass s.reflectedComponent xL =
      current hbar mass s.transmittedComponent xR := by
  rw [s.current_incidentComponent, s.current_reflectedComponent,
    s.current_transmittedComponent]
  have h : 1 - s.R = s.T := by
    linarith [s.R_add_T]
  calc
    (hbar / mass) * s.k + -((hbar / mass) * s.k * s.R) =
        ((hbar / mass) * s.k) * (1 - s.R) := by ring
    _ = (hbar / mass) * s.k * s.T := by rw [h]

/-- Current is not generally additive in waves. Here additivity follows from
the cancellation of counterpropagating interference terms in `flux_freeWave`. -/
lemma current_incident_add_reflected (s : ScatteringLayer) (hbar mass x : ℝ) :
    current hbar mass (fun y => s.incidentComponent y + s.reflectedComponent y) x =
      current hbar mass s.incidentComponent x +
        current hbar mass s.reflectedComponent x := by
  have hsum : (fun y => s.incidentComponent y + s.reflectedComponent y) =
      freeWave s.k 1 s.reflectionAmplitude := by
    funext y
    simp only [incidentComponent, reflectedComponent, freeWave,
      one_mul, zero_mul, add_zero, zero_add]
  rw [hsum, current_freeWave, absSq_one, s.reflectionAmplitude_norm,
    s.current_incidentComponent, s.current_reflectedComponent]
  ring

/-- The physical wave's current agrees everywhere with the transmitted current. -/
lemma current_normalized_eq_transmitted (s : ScatteringLayer) (hbar mass x xR : ℝ) :
    current hbar mass s.normalizedWave x =
      current hbar mass s.transmittedComponent xR := by
  rw [s.current_normalized, s.current_transmittedComponent]

/-- The full scattering wave, including its interior, transports the transmitted
fraction of the incident current. -/
theorem normalized_current_ratio (s : ScatteringLayer) (hbar mass xI x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    current hbar mass s.normalizedWave x /
      current hbar mass s.incidentComponent xI = s.T := by
  rw [s.current_normalized_eq_transmitted hbar mass x x]
  exact s.transmission_eq_current_ratio hbar mass xI x hℏ hm

end ScatteringLayer
end QuantumTunneling
