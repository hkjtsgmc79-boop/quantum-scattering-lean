/- Q2: strengthened endpoint. The original Q1 PublicStatement.lean is preserved.
All proof status must be read from actual execution records, not this filename.
-/
import QuantumTunneling.PublicStatement
import QuantumTunneling.C1Regularity
import QuantumTunneling.Observables
import QuantumTunneling.ScatteringUniqueness

noncomputable section
namespace QuantumTunneling

/-- The original physical scattering statement, strengthened to a globally C¹ wave.
The two finite-potential interfaces remain excluded only from the pointwise
second-derivative equation. -/
theorem finite_barrier_tunneling_C1 (p : Parameters) :
    ∃ (ψ ψD : ℝ → ℂ) (r t : ℂ),
      ContDiff ℝ 1 ψ ∧
      (∀ x, HasDerivAt ψ (ψD x) x) ∧
      (∀ x, x ≠ 0 → x ≠ p.width →
        HasDerivAt ψD (p.spectral.odeCoefficient x • ψ x) x) ∧
      (∀ x, x ≠ 0 → x ≠ p.width →
        (-(p.hbar ^ 2 / (2 * p.mass)) : ℝ) • deriv (deriv ψ) x +
          p.potential x • ψ x = p.energy • ψ x) ∧
      (∀ x, x < 0 → ψ x = plane p.waveNumber x + r * plane (-p.waveNumber) x) ∧
      (∀ x, p.width < x → ψ x = t * plane p.waveNumber (x - p.width)) ∧
      (∀ x, 0 ≤ x → x ≤ p.width →
        ψ x = p.spectral.inside x / p.spectral.incidentAmplitude) ∧
      (∀ x, current p.hbar p.mass ψ x = (p.hbar / p.mass) * p.waveNumber * absSq t) ∧
      (∀ x, 0 < current p.hbar p.mass ψ x) ∧
      absSq r + absSq t = 1 ∧
      (0 < absSq t ∧ absSq t < 1) ∧
      (0 < absSq r ∧ absSq r < 1) ∧
      absSq t =
        (1 + p.height ^ 2 / (4 * p.energy * (p.height - p.energy)) *
          Real.sinh (p.decayNumber * p.width) ^ 2)⁻¹ := by
  refine ⟨p.spectral.normalizedWave, p.spectral.normalizedD,
    p.spectral.reflectionAmplitude, p.spectral.transmissionAmplitude, ?_⟩
  refine ⟨p.spectral.contDiff_one_normalizedWave, p.spectral.hasDerivAt_normalized, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.spectral.hasDerivAt_normalizedD
  · exact p.schrodinger_normalized
  · exact p.spectral.normalized_left
  · exact p.spectral.normalized_right
  · exact p.spectral.normalized_inside
  · intro x
    rw [p.spectral.transmissionAmplitude_norm]
    exact p.spectral.current_normalized p.hbar p.mass x
  · intro x
    exact p.spectral.current_normalized_pos p.hbar p.mass x p.hbar_pos p.mass_pos
  · rw [p.spectral.reflectionAmplitude_norm, p.spectral.transmissionAmplitude_norm]
    exact p.spectral.reflection_add_transmission
  · rw [p.spectral.transmissionAmplitude_norm]
    exact ⟨p.spectral.transmission_pos, p.spectral.transmission_lt_one⟩
  · rw [p.spectral.reflectionAmplitude_norm]
    exact ⟨p.spectral.reflection_pos, p.spectral.reflection_lt_one⟩
  · rw [p.spectral.transmissionAmplitude_norm]
    exact p.transmission_formula

end QuantumTunneling
