/-
Q1 PUBLIC TARGET. All proofs in this release are UNCOMPILED candidates.
This statement must not be weakened to obtain a passing build.
No theorem claims that time-dependent wavepackets or a self-adjoint Hamiltonian
have been constructed. This is the exact below-barrier stationary scattering problem.
-/
import QuantumTunneling.Normalization
import QuantumTunneling.MatchingUniqueness

noncomputable section
namespace QuantumTunneling

/-- Existence of a unit-incident scattering wave for every positive mass, ℏ,
positive finite width, and energy strictly between zero and the barrier height.

The statement explicitly uses actual derivatives, the physical potential,
complex amplitudes and the physical probability current. The Schrödinger
identity is asserted off the two potential discontinuities; the first derivative
exists globally, including both interfaces. -/
theorem finite_barrier_tunneling (p : Parameters) :
    ∃ (ψ ψD : ℝ → ℂ) (r t : ℂ),
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
  refine ⟨p.spectral.hasDerivAt_normalized, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Unbundled entry point: the premises contain only five real parameters and
physical inequalities, with no pre-assumed solution or transmission formula. -/
theorem finite_barrier_transmission_exists
    (hbar mass energy height width : ℝ)
    (hℏ : 0 < hbar) (hm : 0 < mass) (hE : 0 < energy)
    (hEV : energy < height) (ha : 0 < width) :
    ∃ ψ : ℝ → ℂ,
      Differentiable ℝ ψ ∧
      (∀ x, x ≠ 0 → x ≠ width →
        (-(hbar ^ 2 / (2 * mass)) : ℝ) • deriv (deriv ψ) x +
          (if 0 ≤ x ∧ x ≤ width then height else 0) • ψ x = energy • ψ x) ∧
      (∀ x, 0 < current hbar mass ψ x) ∧
      ∃ r t : ℂ,
        (∀ x, x < 0 → ψ x = plane (Real.sqrt (2 * mass * energy) / hbar) x +
          r * plane (-(Real.sqrt (2 * mass * energy) / hbar)) x) ∧
        (∀ x, width < x → ψ x = t *
          plane (Real.sqrt (2 * mass * energy) / hbar) (x - width)) ∧
        absSq r + absSq t = 1 ∧
        (0 < absSq t ∧ absSq t < 1) ∧
        absSq t = (1 + height ^ 2 / (4 * energy * (height - energy)) *
          Real.sinh ((Real.sqrt (2 * mass * (height - energy)) / hbar) * width) ^ 2)⁻¹ := by
  let p : Parameters := ⟨hbar, mass, energy, height, width, hℏ, hm, hE, hEV, ha⟩
  rcases finite_barrier_tunneling p with
    ⟨ψ, ψD, r, t, hd, hdd, hSch, hleft, hright, hinside, hj, hjpos, hsum, hT, hR, hformula⟩
  refine ⟨ψ, (fun x => (hd x).differentiableAt), ?_, hjpos, r, t, ?_, ?_, hsum, hT, ?_⟩
  · exact hSch
  · exact hleft
  · exact hright
  · exact hformula

end QuantumTunneling
