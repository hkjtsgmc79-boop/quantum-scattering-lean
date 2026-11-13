/-
Q4 PUBLIC TARGET. DEVELOPMENT PROOF, NOT YET KERNEL-VERIFIED.
This is the entire positive-energy rectangular-barrier stationary scattering
model: below, above AND exactly at the barrier. No profile, wave, boundary
matching or transmission formula is assumed in the public theorem's premises.
-/
import QuantumTunneling.PhysicalResonance
import QuantumTunneling.Q2Compatibility

noncomputable section
namespace QuantumTunneling

/-- An output specification, not an input hypothesis. -/
structure RectangularScatteringCertificate (p : RectangularParameters)
    (ψ ψD : ℝ → ℂ) (r t : ℂ) : Prop where
  global_C1 : ContDiff ℝ 1 ψ
  derivative : ∀ x, HasDerivAt ψ (ψD x) x
  second_derivative_exists : ∀ x, x ≠ 0 → x ≠ p.width → DifferentiableAt ℝ (deriv ψ) x
  schrodinger : ∀ x, x ≠ 0 → x ≠ p.width →
    (-(p.hbar^2/(2*p.mass)) : ℝ) • deriv (deriv ψ) x+
      p.potential x • ψ x=p.energy • ψ x
  left_scattering : ∀ x, x<0 → ψ x=plane p.k x+r*plane (-p.k) x
  right_scattering : ∀ x, p.width<x → ψ x=t*plane p.k (x-p.width)
  interior : ∀ x, 0≤x → x≤p.width → ψ x=p.layer.inside x/p.layer.A
  current_value : ∀ x, current p.hbar p.mass ψ x=(p.hbar/p.mass)*p.k*absSq t
  current_positive : ∀ x, 0<current p.hbar p.mass ψ x
  conserved_probabilities : absSq r+absSq t=1
  transmission_bounds : 0<absSq t ∧ absSq t≤1
  reflection_bounds : 0≤absSq r ∧ absSq r<1
  below_formula : p.energy<p.height → absSq t=
    (1+p.height^2/(4*p.energy*(p.height-p.energy))*Real.sinh (p.kappa*p.width)^2)⁻¹
  above_formula : p.height<p.energy → absSq t=
    (1+p.height^2/(4*p.energy*(p.energy-p.height))*Real.sin (p.q*p.width)^2)⁻¹
  critical_formula : p.energy=p.height → absSq t=
    (1+p.mass*p.height*p.width^2/(2*p.hbar^2))⁻¹
  above_resonance : p.height<p.energy → (absSq t=1 ↔ Real.sin (p.q*p.width)=0)
  transmission_current_ratio : ∀ xL xR,
    current p.hbar p.mass (fun x=>t*plane p.k (x-p.width)) xR /
      current p.hbar p.mass (plane p.k) xL=absSq t
  reflection_current_ratio : ∀ xL xR,
    -(current p.hbar p.mass (fun x=>r*plane (-p.k) x) xR) /
      current p.hbar p.mass (plane p.k) xL=absSq r

/-- The explicit elementary construction fills every physical output field. -/
theorem complete_rectangular_scattering (p : RectangularParameters) :
    RectangularScatteringCertificate p p.wave p.waveD
      p.reflectionAmplitude p.transmissionAmplitude := by
  constructor
  · exact p.layer.contDiff_one_normalizedWave
  · exact p.layer.hasDerivAt_normalized
  · intro x h0 ha
    change DifferentiableAt ℝ (deriv p.layer.normalizedWave) x
    rw [p.layer.deriv_normalized]
    exact (p.layer.hasDerivAt_normalizedD x h0 ha).differentiableAt
  · exact p.schrodinger_wave
  · exact p.layer.normalized_left
  · exact p.layer.normalized_right
  · exact p.layer.normalized_inside
  · exact p.layer.current_normalized p.hbar p.mass
  · intro x
    exact p.layer.current_normalized_pos p.hbar p.mass x p.hbar_pos p.mass_pos
  · exact p.layer.R_add_T
  · exact ⟨p.layer.T_pos,p.layer.T_le_one⟩
  · exact ⟨p.layer.R_nonneg,p.layer.R_lt_one⟩
  · exact p.transmission_below
  · exact p.transmission_above
  · exact p.transmission_critical
  · exact p.above_resonance_iff
  · intro xL xR
    have hi : p.layer.incidentComponent = plane p.k := by
      funext t
      simp [ScatteringLayer.incidentComponent, freeWave, RectangularParameters.layer]
    have ht : p.layer.transmittedComponent =
        (fun t => p.transmissionAmplitude * plane p.k (t - p.width)) := rfl
    simpa only [hi, ht, RectangularParameters.transmissionAmplitude, ScatteringLayer.T] using
      p.layer.transmission_eq_current_ratio p.hbar p.mass xL xR p.hbar_pos p.mass_pos
  · intro xL xR
    have hi : p.layer.incidentComponent = plane p.k := by
      funext t
      simp [ScatteringLayer.incidentComponent, freeWave, RectangularParameters.layer]
    have hr : p.layer.reflectedComponent =
        (fun t => p.reflectionAmplitude * plane (-p.k) t) := by
      funext t
      simp [ScatteringLayer.reflectedComponent, freeWave, RectangularParameters.layer,
        RectangularParameters.reflectionAmplitude]
    simpa only [hi, hr, RectangularParameters.reflectionAmplitude, ScatteringLayer.R] using
      p.layer.reflection_eq_current_ratio p.hbar p.mass xL xR p.hbar_pos p.mass_pos

/-- The complete project endpoint: constructed wave, unique four-coefficient
matching tuple, and an exhaustive energy-regime formula certificate. -/
theorem rectangular_barrier_project (p : RectangularParameters) :
    RectangularScatteringCertificate p p.wave p.waveD
      p.reflectionAmplitude p.transmissionAmplitude ∧
    p.layer.BoundaryMatched p.reflectionAmplitude p.transmissionAmplitude
      p.transmissionAmplitude (p.transmissionAmplitude*p.layer.exitSlope) ∧
    (∀ r t c d, p.layer.BoundaryMatched r t c d →
      r=p.reflectionAmplitude ∧ t=p.transmissionAmplitude ∧
      c=p.transmissionAmplitude ∧ d=p.transmissionAmplitude*p.layer.exitSlope) :=
  ⟨complete_rectangular_scattering p,p.layer.canonical_boundaryMatched,p.layer.boundaryMatched_unique⟩

/-- Unbundled public theorem: its only premises are five positive real numbers.
Global C1 is explicit; existence of the second derivative is explicit away from
the two jumps; current uses the actual derivative. The threshold is included.
This does not assert a time-dependent wavepacket or Hamiltonian spectral theory. -/
theorem rectangular_barrier_all_positive_energies
    (hbar mass energy height width : ℝ)
    (hℏ : 0<hbar) (hm : 0<mass) (hE : 0<energy) (hV : 0<height) (ha : 0<width) :
    ∃ (ψ ψD : ℝ → ℂ) (r t : ℂ),
      ContDiff ℝ 1 ψ ∧
      (∀ x, HasDerivAt ψ (ψD x) x) ∧
      (∀ x, x ≠ 0 → x ≠ width → DifferentiableAt ℝ (deriv ψ) x) ∧
      (∀ x, x ≠ 0 → x ≠ width →
        (-(hbar^2/(2*mass)) : ℝ) • deriv (deriv ψ) x+
          (if 0≤x ∧ x≤width then height else 0) • ψ x=energy • ψ x) ∧
      (∀ x, x<0 → ψ x=plane (Real.sqrt (2*mass*energy)/hbar) x+
        r*plane (-(Real.sqrt (2*mass*energy)/hbar)) x) ∧
      (∀ x, width<x → ψ x=t*plane (Real.sqrt (2*mass*energy)/hbar) (x-width)) ∧
      (∀ x, current hbar mass ψ x=(hbar/mass)*(Real.sqrt (2*mass*energy)/hbar)*absSq t) ∧
      (∀ x, 0<current hbar mass ψ x) ∧
      absSq r+absSq t=1 ∧ (0<absSq t ∧ absSq t≤1) ∧
      (energy<height → absSq t=
        (1+height^2/(4*energy*(height-energy))*
          Real.sinh ((Real.sqrt (2*mass*(height-energy))/hbar)*width)^2)⁻¹) ∧
      (height<energy → absSq t=
        (1+height^2/(4*energy*(energy-height))*
          Real.sin ((Real.sqrt (2*mass*(energy-height))/hbar)*width)^2)⁻¹) ∧
      (energy=height → absSq t=(1+mass*height*width^2/(2*hbar^2))⁻¹) ∧
      (height<energy → (absSq t=1 ↔
        Real.sin ((Real.sqrt (2*mass*(energy-height))/hbar)*width)=0)) ∧
      (∀ xL xR,
        current hbar mass (fun x=>t*plane (Real.sqrt (2*mass*energy)/hbar) (x-width)) xR /
          current hbar mass (plane (Real.sqrt (2*mass*energy)/hbar)) xL=absSq t) := by
  let p : RectangularParameters := ⟨hbar,mass,energy,height,width,hℏ,hm,hE,hV,ha⟩
  have hc := complete_rectangular_scattering p
  exact ⟨p.wave,p.waveD,p.reflectionAmplitude,p.transmissionAmplitude,
    hc.global_C1,hc.derivative,hc.second_derivative_exists,hc.schrodinger,
    hc.left_scattering,hc.right_scattering,hc.current_value,hc.current_positive,
    hc.conserved_probabilities,hc.transmission_bounds,hc.below_formula,hc.above_formula,
    hc.critical_formula,hc.above_resonance,hc.transmission_current_ratio⟩

end QuantumTunneling
