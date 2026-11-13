/- Q2: restore physical constants and prove the exact Schrödinger equation. -/
import QuantumTunneling.Gluing
import QuantumTunneling.Probabilities

noncomputable section
namespace QuantumTunneling
namespace Parameters

lemma coefficient_physical (p : Parameters) :
    p.spectral.sigma ^ 2 = p.height ^ 2 / (4 * p.energy * (p.height - p.energy)) := by
  rw [Spectral.sigma_sq]
  change (p.waveNumber ^ 2 + p.decayNumber ^ 2) ^ 2 /
    (4 * p.waveNumber ^ 2 * p.decayNumber ^ 2) = _
  rw [p.waveNumber_sq, p.decayNumber_sq]
  field_simp [ne_of_gt p.hbar_pos, ne_of_gt p.mass_pos,
    ne_of_gt p.energy_pos, ne_of_gt p.gap_pos]
  <;> ring

lemma transmission_formula (p : Parameters) :
    p.spectral.transmission =
      (1 + p.height ^ 2 / (4 * p.energy * (p.height - p.energy)) *
        Real.sinh (p.decayNumber * p.width) ^ 2)⁻¹ := by
  rw [Spectral.transmission_closed, p.coefficient_physical]
  rfl

lemma odeCoefficient_energy (p : Parameters) (x : ℝ)
    (h0 : x ≠ 0) (ha : x ≠ p.width) :
    -(p.hbar ^ 2 / (2 * p.mass)) * p.spectral.odeCoefficient x + p.potential x =
      p.energy := by
  have hk := p.kinetic_waveNumber
  have hκ := p.kinetic_decayNumber
  by_cases hx : x < 0
  · simp [Spectral.odeCoefficient, spectral, potential, hx, not_le.mpr hx]
    nlinarith
  · have hx' : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm h0)
    by_cases hxa : x < p.width
    · simp [Spectral.odeCoefficient, spectral, potential, hx, hxa, le_of_lt hx', le_of_lt hxa]
      linarith
    · have hax : p.width < x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm ha)
      simp [Spectral.odeCoefficient, spectral, potential, hx, hxa, not_le.mpr hax]
      nlinarith

/-- Literal second derivative in physical space, off the two finite jumps. -/
lemma schrodinger_wave (p : Parameters) (x : ℝ)
    (h0 : x ≠ 0) (ha : x ≠ p.width) :
    (-(p.hbar ^ 2 / (2 * p.mass)) : ℝ) • deriv (deriv p.spectral.wave) x +
      p.potential x • p.spectral.wave x = p.energy • p.spectral.wave x := by
  rw [p.spectral.second_deriv_wave x h0 ha, smul_smul, ← add_smul,
    p.odeCoefficient_energy x h0 ha]

end Parameters
end QuantumTunneling
