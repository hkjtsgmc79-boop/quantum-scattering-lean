/-
Q2: physical reflection and transmission as ratios of actual currents.
Consult STATUS.json and reports for the complete fixed-version build and axiom checks.
-/
import QuantumTunneling.Normalization

/-!
# Currents of the incident, reflected and transmitted components

The formulas in `Probabilities` already express the expected flux ratios.
Here each flux is obtained from `current`, hence from the actual real derivative
of its complex-valued component wave. In the present model both exterior
potentials are zero, the mass is common, and the two exterior wave numbers are
the same positive `k`. Thus the common factor `hbar * k / mass` cancels. This
does not assert that squared amplitudes alone give transmission when exterior
wave numbers or masses differ.

The component formulas extend to all real `x` to make their derivatives simple.
Their interpretation as the asymptotic pieces of the physical solution is
specified separately on `x < 0` and `a < x`.
-/
noncomputable section
namespace QuantumTunneling
namespace Spectral

/-- The unit-amplitude incoming component on the left. -/
def incidentComponent (s : Spectral) : ℝ → ℂ := freeWave s.k 1 0

/-- The outgoing reflected component on the left, with negative wave number. -/
def reflectedComponent (s : Spectral) : ℝ → ℂ :=
  freeWave s.k 0 s.reflectionAmplitude

/-- The outgoing transmitted component, with its phase anchored at the exit. -/
def transmittedComponent (s : Spectral) (x : ℝ) : ℂ :=
  s.transmissionAmplitude * s.right x

lemma normalized_left_components (s : Spectral) (x : ℝ) (hx : x < 0) :
    s.normalizedWave x = s.incidentComponent x + s.reflectedComponent x := by
  simpa only [incidentComponent, reflectedComponent, freeWave,
    one_mul, zero_mul, add_zero, zero_add] using s.normalized_left x hx

lemma normalized_right_component (s : Spectral) (x : ℝ) (hx : s.a < x) :
    s.normalizedWave x = s.transmittedComponent x := by
  exact s.normalized_right x hx

/-- The incoming-from-the-right coefficient is explicitly zero. -/
lemma normalized_right_outgoing_only (s : Spectral) (x : ℝ) (hx : s.a < x) :
    s.normalizedWave x = freeWave s.k s.transmissionAmplitude 0 (x - s.a) := by
  simpa only [freeWave, zero_mul, add_zero] using s.normalized_right x hx

/-- The unit incident flux, computed using the actual derivative. -/
lemma current_incidentComponent (s : Spectral) (hbar mass x : ℝ) :
    current hbar mass s.incidentComponent x = (hbar / mass) * s.k := by
  simp only [incidentComponent, current_freeWave, absSq_one, absSq_zero,
    sub_zero, mul_one]

/-- Reflected current is signed: it points toward decreasing x. -/
lemma current_reflectedComponent (s : Spectral) (hbar mass x : ℝ) :
    current hbar mass s.reflectedComponent x =
      -((hbar / mass) * s.k * s.reflection) := by
  rw [reflectedComponent, current_freeWave, absSq_zero, s.reflectionAmplitude_norm]
  ring

/-- The exit component uses the derivative of the shifted plane wave. -/
lemma current_transmittedComponent (s : Spectral) (hbar mass x : ℝ) :
    current hbar mass s.transmittedComponent x =
      (hbar / mass) * s.k * s.transmission := by
  have hd := (s.hasDerivAt_right x).const_mul s.transmissionAmplitude
  change (hbar / mass) * fluxForm (s.transmissionAmplitude * s.right x)
    (deriv (fun y => s.transmissionAmplitude * s.right y) x) = _
  rw [hd.deriv, fluxForm_scale, s.flux_right, s.transmissionAmplitude_norm]
  ring

lemma current_incidentComponent_pos (s : Spectral) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < current hbar mass s.incidentComponent x := by
  rw [s.current_incidentComponent]
  exact mul_pos (div_pos hℏ hm) s.k_pos

lemma current_reflectedComponent_neg (s : Spectral) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    current hbar mass s.reflectedComponent x < 0 := by
  rw [s.current_reflectedComponent]
  have h : 0 < (hbar / mass) * s.k * s.reflection :=
    mul_pos (mul_pos (div_pos hℏ hm) s.k_pos) s.reflection_pos
  linarith

lemma current_transmittedComponent_pos (s : Spectral) (hbar mass x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    0 < current hbar mass s.transmittedComponent x := by
  rw [s.current_transmittedComponent]
  exact mul_pos (mul_pos (div_pos hℏ hm) s.k_pos) s.transmission_pos

/-- The physical transmitted/incident current ratio is exactly T. The sample
points may differ because each component current is spatially constant. -/
theorem transmission_eq_current_ratio (s : Spectral) (hbar mass xL xR : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    current hbar mass s.transmittedComponent xR /
      current hbar mass s.incidentComponent xL = s.transmission := by
  rw [s.current_transmittedComponent, s.current_incidentComponent]
  have hfactor : (hbar / mass) * s.k ≠ 0 :=
    ne_of_gt (mul_pos (div_pos hℏ hm) s.k_pos)
  apply (div_eq_iff hfactor).2
  ring

/-- Reflection is the magnitude of the negative reflected current divided by
the positive incident current. The minus sign is essential. -/
theorem reflection_eq_current_ratio (s : Spectral) (hbar mass xI xR : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    -(current hbar mass s.reflectedComponent xR) /
      current hbar mass s.incidentComponent xI = s.reflection := by
  rw [s.current_reflectedComponent, s.current_incidentComponent]
  have hfactor : (hbar / mass) * s.k ≠ 0 :=
    ne_of_gt (mul_pos (div_pos hℏ hm) s.k_pos)
  apply (div_eq_iff hfactor).2
  ring

/-- Net left current equals transmitted current; reflected current is signed. -/
theorem component_current_balance (s : Spectral) (hbar mass xL xR : ℝ) :
    current hbar mass s.incidentComponent xL +
        current hbar mass s.reflectedComponent xL =
      current hbar mass s.transmittedComponent xR := by
  rw [s.current_incidentComponent, s.current_reflectedComponent,
    s.current_transmittedComponent]
  have h : 1 - s.reflection = s.transmission := by
    linarith [s.reflection_add_transmission]
  calc
    (hbar / mass) * s.k + -((hbar / mass) * s.k * s.reflection) =
        ((hbar / mass) * s.k) * (1 - s.reflection) := by ring
    _ = (hbar / mass) * s.k * s.transmission := by rw [h]

/-- Current is not generally additive in waves. Here additivity follows from
the cancellation of counterpropagating interference terms in `flux_freeWave`. -/
lemma current_incident_add_reflected (s : Spectral) (hbar mass x : ℝ) :
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
lemma current_normalized_eq_transmitted (s : Spectral) (hbar mass x xR : ℝ) :
    current hbar mass s.normalizedWave x =
      current hbar mass s.transmittedComponent xR := by
  rw [s.current_normalized, s.current_transmittedComponent]

/-- The full scattering wave, including its interior, transports the transmitted
fraction of the incident current. -/
theorem normalized_current_ratio (s : Spectral) (hbar mass xI x : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) :
    current hbar mass s.normalizedWave x /
      current hbar mass s.incidentComponent xI = s.transmission := by
  rw [s.current_normalized_eq_transmitted hbar mass x x]
  exact s.transmission_eq_current_ratio hbar mass xI x hℏ hm

end Spectral
namespace Parameters

/-- The measured transmitted/incident current ratio has the textbook expression.
The proof uses the already constructed wave and the nonzero incoming current. -/
theorem physical_transmission_current_formula (p : Parameters) (xL xR : ℝ) :
    current p.hbar p.mass p.spectral.transmittedComponent xR /
      current p.hbar p.mass p.spectral.incidentComponent xL =
      (1 + p.height ^ 2 / (4 * p.energy * (p.height - p.energy)) *
        Real.sinh (p.decayNumber * p.width) ^ 2)⁻¹ := by
  rw [p.spectral.transmission_eq_current_ratio p.hbar p.mass xL xR
    p.hbar_pos p.mass_pos]
  exact p.transmission_formula

/-- Observable reflection and transmission, with physically located left/right
sample points and the asymptotic wave decompositions explicitly attached. -/
theorem physical_current_certificate (p : Parameters) (xL xR : ℝ)
    (hL : xL < 0) (hR : p.width < xR) :
    p.spectral.normalizedWave xL =
        p.spectral.incidentComponent xL + p.spectral.reflectedComponent xL ∧
    p.spectral.normalizedWave xR = p.spectral.transmittedComponent xR ∧
    0 < current p.hbar p.mass p.spectral.incidentComponent xL ∧
    current p.hbar p.mass p.spectral.reflectedComponent xL < 0 ∧
    0 < current p.hbar p.mass p.spectral.transmittedComponent xR ∧
    current p.hbar p.mass p.spectral.transmittedComponent xR /
        current p.hbar p.mass p.spectral.incidentComponent xL =
      p.spectral.transmission ∧
    -(current p.hbar p.mass p.spectral.reflectedComponent xL) /
        current p.hbar p.mass p.spectral.incidentComponent xL =
      p.spectral.reflection ∧
    current p.hbar p.mass p.spectral.incidentComponent xL +
        current p.hbar p.mass p.spectral.reflectedComponent xL =
      current p.hbar p.mass p.spectral.transmittedComponent xR := by
  exact ⟨p.spectral.normalized_left_components xL hL,
    p.spectral.normalized_right_component xR hR,
    p.spectral.current_incidentComponent_pos p.hbar p.mass xL p.hbar_pos p.mass_pos,
    p.spectral.current_reflectedComponent_neg p.hbar p.mass xL p.hbar_pos p.mass_pos,
    p.spectral.current_transmittedComponent_pos p.hbar p.mass xR p.hbar_pos p.mass_pos,
    p.spectral.transmission_eq_current_ratio p.hbar p.mass xL xR p.hbar_pos p.mass_pos,
    p.spectral.reflection_eq_current_ratio p.hbar p.mass xL xL p.hbar_pos p.mass_pos,
    p.spectral.component_current_balance p.hbar p.mass xL xR⟩

end Parameters
end QuantumTunneling
