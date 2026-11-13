/-
Q2: uniqueness of all four coefficients in the finite-barrier scattering ansatz.
The boundary conditions use actual `deriv`, not independently stipulated slopes.
This is uniqueness within the stated constant-coefficient two-mode ansatz;
it does not assert an arbitrary-function ODE uniqueness or spectral theorem.
-/
import QuantumTunneling.Normalization
import QuantumTunneling.MatchingUniqueness

noncomputable section
namespace QuantumTunneling
namespace Spectral

/-- General interior solution, in the exit-anchored hyperbolic basis. -/
def barrierCombination (s : Spectral) (C D : ℂ) (x : ℝ) : ℂ :=
  C * (Real.cosh (s.κ * (x - s.a)) : ℂ) +
    D * (Real.sinh (s.κ * (x - s.a)) : ℂ)

def barrierCombinationD (s : Spectral) (C D : ℂ) (x : ℝ) : ℂ :=
  C * ((s.κ * Real.sinh (s.κ * (x - s.a)) : ℝ) : ℂ) +
    D * ((s.κ * Real.cosh (s.κ * (x - s.a)) : ℝ) : ℂ)

def exitSlope (s : Spectral) : ℂ := ((s.k / s.κ : ℝ) : ℂ) * Complex.I

lemma hasDerivAt_barrierCombination (s : Spectral) (C D : ℂ) (x : ℝ) :
    HasDerivAt (s.barrierCombination C D) (s.barrierCombinationD C D x) x := by
  have hp : HasDerivAt (fun y : ℝ => s.κ * (y - s.a)) s.κ x := by
    simpa using ((hasDerivAt_id x).sub_const s.a).const_mul s.κ
  have hd := (hp.cosh.ofReal_comp.const_mul C).add (hp.sinh.ofReal_comp.const_mul D)
  convert hd using 1
  · rfl
  · simp only [barrierCombinationD, Complex.ofReal_mul]
    ring

lemma deriv_barrierCombination (s : Spectral) (C D : ℂ) (x : ℝ) :
    deriv (s.barrierCombination C D) x = s.barrierCombinationD C D x :=
  (s.hasDerivAt_barrierCombination C D x).deriv

@[simp] lemma barrierCombination_at_exit (s : Spectral) (C D : ℂ) :
    s.barrierCombination C D s.a = C := by
  simp [barrierCombination]

@[simp] lemma barrierCombinationD_at_exit (s : Spectral) (C D : ℂ) :
    s.barrierCombinationD C D s.a = D * (s.κ : ℂ) := by
  simp [barrierCombinationD]

lemma barrierCombination_scaled (s : Spectral) (t : ℂ) (x : ℝ) :
    s.barrierCombination t (t * s.exitSlope) x = t * s.inside x := by
  apply Complex.ext <;>
    simp only [barrierCombination, exitSlope, inside, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;>
    ring

lemma barrierCombinationD_scaled (s : Spectral) (t : ℂ) (x : ℝ) :
    s.barrierCombinationD t (t * s.exitSlope) x = t * s.insideD x := by
  apply Complex.ext <;>
    simp only [barrierCombinationD, exitSlope, insideD, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;>
    field_simp [ne_of_gt s.κ_pos] <;> ring

/-- Both values and actual derivatives match at both interfaces. Unit incoming
amplitude and no incoming wave on the right are part of the scattering ansatz. -/
structure BoundaryMatched (s : Spectral) (r t C D : ℂ) : Prop where
  left_value : freeWave s.k 1 r 0 = s.barrierCombination C D 0
  left_derivative : deriv (freeWave s.k 1 r) 0 = deriv (s.barrierCombination C D) 0
  right_value : s.barrierCombination C D s.a = t * s.right s.a
  right_derivative : deriv (s.barrierCombination C D) s.a =
    deriv (fun x => t * s.right x) s.a

lemma boundaryMatched_exit (s : Spectral) (r t C D : ℂ)
    (h : s.BoundaryMatched r t C D) : C = t ∧ D = t * s.exitSlope := by
  have hC : C = t := by simpa using h.right_value
  have hd := h.right_derivative
  rw [s.deriv_barrierCombination,
    ((s.hasDerivAt_right s.a).const_mul t).deriv,
    s.barrierCombinationD_at_exit, s.rightD_at_exit] at hd
  have hκ : (s.κ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt s.κ_pos)
  refine ⟨hC, ?_⟩
  calc
    D = (t * ((s.k : ℂ) * Complex.I)) / (s.κ : ℂ) := (eq_div_iff hκ).2 hd
    _ = t * s.exitSlope := by simp [exitSlope, Complex.ofReal_div] <;> ring

lemma freeWave_scaled (s : Spectral) (t : ℂ) (x : ℝ) :
    freeWave s.k (t * s.incidentAmplitude) (t * s.reflectedAmplitude) x =
      t * s.left x := by
  simp only [left, freeWave]
  ring

lemma freeWaveD_scaled (s : Spectral) (t : ℂ) (x : ℝ) :
    freeWaveD s.k (t * s.incidentAmplitude) (t * s.reflectedAmplitude) x =
      t * s.leftD x := by
  simp only [leftD, freeWaveD]
  ring

/-- All four coefficients are fixed by the four interface equations. The
nonzero incident denominator is derived in Q1, not assumed here. -/
theorem boundaryMatched_unique (s : Spectral) (r t C D : ℂ)
    (h : s.BoundaryMatched r t C D) :
    r = s.reflectionAmplitude ∧ t = s.transmissionAmplitude ∧
      C = s.transmissionAmplitude ∧ D = s.transmissionAmplitude * s.exitSlope := by
  obtain ⟨hC, hD⟩ := s.boundaryMatched_exit r t C D h
  have hv := h.left_value
  rw [hC, hD, s.barrierCombination_scaled] at hv
  have hd := h.left_derivative
  rw [(hasDerivAt_freeWave s.k 1 r 0).deriv, s.deriv_barrierCombination,
    hC, hD, s.barrierCombinationD_scaled] at hd
  have hv' : freeWave s.k 1 r 0 =
      freeWave s.k (t * s.incidentAmplitude) (t * s.reflectedAmplitude) 0 := by
    rw [s.freeWave_scaled, s.match_left_value]
    exact hv
  have hd' : freeWaveD s.k 1 r 0 =
      freeWaveD s.k (t * s.incidentAmplitude) (t * s.reflectedAmplitude) 0 := by
    rw [s.freeWaveD_scaled, s.match_left_derivative]
    exact hd
  obtain ⟨hA, hB⟩ := free_coefficients_unique s.k (ne_of_gt s.k_pos)
    1 r (t * s.incidentAmplitude) (t * s.reflectedAmplitude) hv' hd'
  have ht : t = s.transmissionAmplitude := by
    exact (eq_div_iff s.incident_ne_zero).2 hA.symm
  have hr : r = s.reflectionAmplitude := by
    rw [hB, ht]
    unfold transmissionAmplitude reflectionAmplitude
    ring
  exact ⟨hr, ht, hC.trans ht, hD.trans (congrArg (fun z => z * s.exitSlope) ht)⟩

lemma normalized_freeWave (s : Spectral) (x : ℝ) :
    freeWave s.k 1 s.reflectionAmplitude x = s.transmissionAmplitude * s.left x := by
  simp only [left, freeWave, reflectionAmplitude, transmissionAmplitude]
  field_simp [s.incident_ne_zero] <;> ring

lemma normalized_freeWaveD (s : Spectral) (x : ℝ) :
    freeWaveD s.k 1 s.reflectionAmplitude x = s.transmissionAmplitude * s.leftD x := by
  simp only [leftD, freeWaveD, reflectionAmplitude, transmissionAmplitude]
  field_simp [s.incident_ne_zero] <;> ring

/-- The uniquely specified coefficient tuple actually satisfies all conditions. -/
theorem canonical_boundaryMatched (s : Spectral) :
    s.BoundaryMatched s.reflectionAmplitude s.transmissionAmplitude
      s.transmissionAmplitude (s.transmissionAmplitude * s.exitSlope) := by
  constructor
  · rw [s.normalized_freeWave, s.barrierCombination_scaled, s.match_left_value]
  · rw [(hasDerivAt_freeWave s.k 1 s.reflectionAmplitude 0).deriv,
      s.deriv_barrierCombination, s.normalized_freeWaveD,
      s.barrierCombinationD_scaled, s.match_left_derivative]
  · rw [s.barrierCombination_scaled, s.match_right_value]
  · rw [s.deriv_barrierCombination, s.barrierCombinationD_scaled,
      ((s.hasDerivAt_right s.a).const_mul s.transmissionAmplitude).deriv,
      s.match_right_derivative]

theorem boundaryMatched_iff (s : Spectral) (r t C D : ℂ) :
    s.BoundaryMatched r t C D ↔
    r = s.reflectionAmplitude ∧ t = s.transmissionAmplitude ∧
      C = s.transmissionAmplitude ∧ D = s.transmissionAmplitude * s.exitSlope := by
  constructor
  · exact s.boundaryMatched_unique r t C D
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact s.canonical_boundaryMatched

end Spectral
end QuantumTunneling
