/- Q5: current conservation for arbitrary classical states and two-sided input.
No assumption that probability currents add for arbitrary superposed waves. -/
import QuantumTunneling.GeneralScatteringUniqueness

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumTunneling

lemma fluxForm_derivative_zero {f v : ℝ→ℂ} {x c : ℝ}
    (hf : HasDerivAt f (v x) x) (hv : HasDerivAt v (c • f x) x) :
    HasDerivAt (fun y=>fluxForm (f y) (v y)) 0 x := by
  have hfr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hfi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hvr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hv
  have hvi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hv
  have h := (hfr.mul hvi).sub (hfi.mul hvr)
  convert h using 1
  · rfl
  · simp [Function.comp_def, Complex.real_smul, Complex.mul_re, Complex.mul_im]
    ring

namespace StationaryState
lemma continuous_current {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) : Continuous (current p.hbar p.mass f) := by
  unfold current fluxForm
  exact continuous_const.mul
    (((Complex.continuous_re.comp h.continuous).mul
      (Complex.continuous_im.comp h.continuous_derivative)).sub
    ((Complex.continuous_im.comp h.continuous).mul
      (Complex.continuous_re.comp h.continuous_derivative)))

theorem current_constant {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) (x y : ℝ) :
    current p.hbar p.mass f x=current p.hbar p.mass f y := by
  have hd : ∀ z, z≠0 → z≠p.width → HasDerivAt (current p.hbar p.mass f) 0 z := by
    intro z h0 ha
    change HasDerivAt (fun t => (p.hbar/p.mass) * fluxForm (f t) (deriv f t)) 0 z
    simpa using
      (fluxForm_derivative_zero (h.hasDerivAt z) (h.equation z h0 ha)).const_mul (p.hbar/p.mass)
  exact (constant_across_two_interfaces p.width_pos h.continuous_current hd x).trans
    (constant_across_two_interfaces p.width_pos h.continuous_current hd y).symm
end StationaryState

/-- Actual probability current of a simultaneous left/right scattering state. -/
theorem coherent_current_value (p : RectangularParameters) (iL iR : ℂ) (x : ℝ) :
    current p.hbar p.mass (p.coherentWave iL iR) x =
      (p.hbar/p.mass)*p.k*(absSq iL-absSq (p.layer.outgoingLeft iL iR)) := by
  have h := coherentWave_radiation p iL iR
  have hstate := p.coherentWave_stationary iL iR
  rw [hstate.current_constant x (-1)]
  rw [current,(h.hasDerivAt_left (-1) (by norm_num)).deriv,
    h.left (-1) (by norm_num),flux_freeWave]
  ring

/-- The right exterior gives the same flux, with its correct channel signs. -/
theorem coherent_current_right (p : RectangularParameters) (iL iR : ℂ) (x : ℝ) :
    current p.hbar p.mass (p.coherentWave iL iR) x =
      (p.hbar/p.mass)*p.k*(absSq (p.layer.outgoingRight iL iR)-absSq iR) := by
  rw [coherent_current_value]
  have h := p.layer.coherent_probability_balance iL iR
  congr 1
  linarith

/-- No outgoing-only nonzero solution: a useful uniqueness corollary. -/
theorem no_outgoing_only_solution (p : RectangularParameters) (f : ℝ→ℂ)
    (hf : AdmissibleScattering p 0 0 f) : f=0 := by
  obtain ⟨oL,oR,hr⟩ := hf.2
  have he := scattering_state_unique hf.1 (p.coherentWave_stationary 0 0) hr
    (coherentWave_radiation p 0 0)
  rw [he]
  funext x
  simp [RectangularParameters.coherentWave]

end QuantumTunneling
