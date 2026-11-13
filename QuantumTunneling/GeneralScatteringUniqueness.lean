/-
Q5: uniqueness among ALL classical scattering functions satisfying the ODE and
exterior radiation conditions. No assumption of an interior basis expansion.
Candidate proof source; dependencies and tactics await fixed-version execution.
-/
import QuantumTunneling.TwoSidedStates

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumTunneling

namespace StationaryState
/-- The physical Schrödinger equation is sufficient for our first-order state
predicate; no extra dynamical law is hidden in its coefficient interface. -/
lemma of_schrodinger {p : RectangularParameters} {f : ℝ→ℂ}
    (hC : ContDiff ℝ 1 f)
    (hD : ∀ x, x≠0 → x≠p.width → DifferentiableAt ℝ (deriv f) x)
    (hS : ∀ x, x≠0 → x≠p.width →
      (-p.kinetic) • deriv (deriv f) x+p.potential x • f x=p.energy • f x) :
    StationaryState p f := by
  refine ⟨hC, ?_⟩
  intro x h0 ha
  have hp : 0<p.kinetic := by
    exact div_pos (pow_pos p.hbar_pos 2) (mul_pos (by norm_num) p.mass_pos)
  have hc := p.odeCoefficient_energy x h0 ha
  have he : (-p.kinetic) • deriv (deriv f) x=
      (-p.kinetic) • (p.layer.odeCoefficient x • f x) := by
    calc
      _ = p.energy • f x-p.potential x • f x := eq_sub_iff_add_eq.mpr (hS x h0 ha)
      _ = (p.energy-p.potential x) • f x := (sub_smul _ _ _).symm
      _ = _ := by rw [smul_smul]; congr 1; linarith
  have he' := congrArg (fun z:ℂ => (-p.kinetic)⁻¹ • z) he
  have hx : deriv (deriv f) x=p.layer.odeCoefficient x • f x := by
    simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr (ne_of_gt hp)),one_mul,one_smul] using he'
  simpa only [hx] using (hD x h0 ha).hasDerivAt

lemma interior_ode {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) (x : ℝ) (hx : x∈Ioo 0 p.width) :
    HasDerivAt (deriv f) (-p.profile.delta • f x) x := by
  simpa [ScatteringLayer.odeCoefficient,RectangularParameters.layer,
    not_lt.mpr (le_of_lt hx.1),hx.2] using
    h.equation x (ne_of_gt hx.1) (ne_of_lt hx.2)

/-- Representation on the entire barrier follows from the ODE and C1 traces. -/
theorem interior_representation {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) (x : ℝ) (hx : x∈Icc 0 p.width) :
    f x=f p.width*(p.profile.C (x-p.width):ℂ)+
      deriv f p.width*(p.profile.S (x-p.width):ℂ) ∧
    deriv f x=-(p.profile.delta:ℂ)*f p.width*(p.profile.S (x-p.width):ℂ)+
      deriv f p.width*(p.profile.C (x-p.width):ℂ) := by
  exact p.profile.representation_on_closed_interval p.width_pos
    ⟨le_of_lt p.width_pos,le_rfl⟩ f (deriv f) h.continuous h.continuous_derivative
    (fun y _ => h.hasDerivAt y) h.interior_ode x hx
end StationaryState

namespace TwoSidedRadiation
lemma hasDerivAt_left {p : RectangularParameters} {f : ℝ→ℂ}
    {iL iR oL oR : ℂ} (h : TwoSidedRadiation p f iL iR oL oR)
    (x : ℝ) (hx : x<0) : HasDerivAt f (freeWaveD p.k iL oL x) x := by
  apply (hasDerivAt_freeWave p.k iL oL x).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact h.left y hy

lemma hasDerivAt_right {p : RectangularParameters} {f : ℝ→ℂ}
    {iL iR oL oR : ℂ} (h : TwoSidedRadiation p f iL iR oL oR)
    (x : ℝ) (hx : p.width<x) :
    HasDerivAt f (freeWaveD p.k oR iR (x-p.width)) x := by
  have hd : HasDerivAt (fun y=>freeWave p.k oR iR (y-p.width))
      (freeWaveD p.k oR iR (x-p.width)) x := by
    simpa [Function.comp_def] using (hasDerivAt_freeWave p.k oR iR (x-p.width)).scomp x
      ((hasDerivAt_id x).sub_const p.width)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact h.right y hy

/-- C1 matching at an interface is derived from the global regularity and open
exterior radiation conditions; it is not supplied as an extra assumption. -/
lemma endpoint_traces {p : RectangularParameters} {f : ℝ→ℂ}
    {iL iR oL oR : ℂ} (h : TwoSidedRadiation p f iL iR oL oR)
    (hs : StationaryState p f) :
    f 0=iL+oL ∧ deriv f 0=(p.k:ℂ)*Complex.I*(iL-oL) ∧
    f p.width=oR+iR ∧ deriv f p.width=(p.k:ℂ)*Complex.I*(oR-iR) := by
  have hfree : Continuous (freeWave p.k iL oL) :=
    (show Differentiable ℝ (freeWave p.k iL oL) from
      fun x=>(hasDerivAt_freeWave p.k iL oL x).differentiableAt).continuous
  have hfreeD : Continuous (freeWaveD p.k iL oL) :=
    (show Differentiable ℝ (freeWaveD p.k iL oL) from
      fun x=>(hasDerivAt_freeWaveD p.k iL oL x).differentiableAt).continuous
  have hrfree : Continuous (fun x=>freeWave p.k oR iR (x-p.width)) :=
    ((show Differentiable ℝ (freeWave p.k oR iR) from
      fun x=>(hasDerivAt_freeWave p.k oR iR x).differentiableAt).continuous).comp
      (continuous_id.sub continuous_const)
  have hrfreeD : Continuous (fun x=>freeWaveD p.k oR iR (x-p.width)) :=
    ((show Differentiable ℝ (freeWaveD p.k oR iR) from
      fun x=>(hasDerivAt_freeWaveD p.k oR iR x).differentiableAt).continuous).comp
      (continuous_id.sub continuous_const)
  have h0 := continuous_eq_at_left_endpoint hs.continuous hfree 0 h.left
  have hd0 := continuous_eq_at_left_endpoint hs.continuous_derivative hfreeD 0
    (fun x hx=>(h.hasDerivAt_left x hx).deriv)
  have ha := continuous_eq_at_right_endpoint hs.continuous hrfree p.width h.right
  have hda := continuous_eq_at_right_endpoint hs.continuous_derivative hrfreeD p.width
    (fun x hx=>(h.hasDerivAt_right x hx).deriv)
  refine ⟨by simpa [freeWave] using h0, ?_, by simpa [freeWave] using ha, ?_⟩
  · rw [hd0]
    simp [freeWaveD, planeD]
    ring
  · rw [hda]
    simp [freeWaveD, planeD]
    ring
end TwoSidedRadiation

namespace ScatteringLayer
lemma transfer_scalar_balance (s : ScatteringLayer) : s.B^2+star s.A*s.A=1 := by
  have hB := star_mul_self_absSq s.B
  rw [s.B_pure_imaginary] at hB
  have hA := star_mul_self_absSq s.A
  have hi : (absSq s.A:ℂ)-(absSq s.B:ℂ)=1 := by exact_mod_cast s.amplitude_balance
  linear_combination hA - hB + hi

/-- Solve the transfer equations with BOTH incoming amplitudes unrestricted. -/
lemma solve_two_port (s : ScatteringLayer) (iL iR oL oR : ℂ)
    (h1 : iL=s.A*oR-s.B*iR) (h2 : oL=s.B*oR+star s.A*iR) :
    oL=s.outgoingLeft iL iR ∧ oR=s.outgoingRight iL iR := by
  have hr : oR=(iL+s.B*iR)/s.A := by
    apply (eq_div_iff s.A_ne_zero).2
    linear_combination -h1
  constructor
  · rw [h2,hr]
    unfold outgoingLeft reflectionAmplitude transmissionAmplitude
    field_simp [s.A_ne_zero]
    linear_combination iR*s.transfer_scalar_balance
  · rw [hr]
    unfold outgoingRight transmissionAmplitude reflectionAmplitude
    ring
end ScatteringLayer

/-- The ODE implies the transfer equations for any classical scattering state. -/
theorem radiation_transfer_equations {p : RectangularParameters} {f : ℝ→ℂ}
    {iL iR oL oR : ℂ} (hs : StationaryState p f)
    (hr : TwoSidedRadiation p f iL iR oL oR) :
    iL=p.layer.A*oR-p.layer.B*iR ∧ oL=p.layer.B*oR+star p.layer.A*iR := by
  obtain ⟨h0,hd0,ha,hda⟩ := hr.endpoint_traces hs
  obtain ⟨hv,hd⟩ := hs.interior_representation 0 ⟨le_rfl,le_of_lt p.width_pos⟩
  rw [h0,ha,hda,zero_sub,p.profile.C_neg,p.profile.S_neg] at hv
  rw [hd0,ha,hda,zero_sub,p.profile.C_neg,p.profile.S_neg] at hd
  have hscale : (2*(p.k:ℂ)*Complex.I)*
      (iL-(p.layer.A*oR-p.layer.B*iR))=0 := by
    calc
      _ = ((p.k:ℂ)*Complex.I)*
          (iL+oL-((oR+iR)*(p.profile.C p.width:ℂ)+
            ((p.k:ℂ)*Complex.I*(oR-iR))*(-(p.profile.S p.width:ℂ))))+
        ((p.k:ℂ)*Complex.I*(iL-oL)-
          (-(p.profile.delta:ℂ)*(oR+iR)*(-(p.profile.S p.width:ℂ))+
            ((p.k:ℂ)*Complex.I*(oR-iR))*(p.profile.C p.width:ℂ))) := by
        simp only [ScatteringLayer.A,ScatteringLayer.B,ScatteringLayer.alpha,
          ScatteringLayer.beta,RectangularParameters.layer,Complex.mk_eq_add_mul_I]
        push_cast
        field_simp [ne_of_gt p.k_pos]
        ring_nf
        simp [Complex.I_sq] <;> ring
      _ = 0 := by rw [hv,hd]; push_cast; ring
  have hfac : 2*(p.k:ℂ)*Complex.I≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt p.k_pos)) Complex.I_ne_zero
  have hi : iL=p.layer.A*oR-p.layer.B*iR :=
    sub_eq_zero.mp ((mul_eq_zero.mp hscale).resolve_left hfac)
  refine ⟨hi, ?_⟩
  calc
    oL = (oR+iR)*(p.profile.C p.width:ℂ)+
      ((p.k:ℂ)*Complex.I*(oR-iR))*(-(p.profile.S p.width:ℂ))-iL := by
        push_cast at hv; linear_combination hv
    _ = p.layer.B*oR+star p.layer.A*iR := by
      rw [hi]
      apply Complex.ext <;>
        simp [ScatteringLayer.A,ScatteringLayer.B,ScatteringLayer.alpha,
          ScatteringLayer.beta,RectangularParameters.layer,Complex.mul_re,Complex.mul_im]
        <;> field_simp [ne_of_gt p.k_pos] <;> ring

/-- Outgoing amplitudes are determined for arbitrary functions, not merely for
solutions guessed to be linear combinations of the elementary basis. -/
theorem general_outgoing_amplitudes {p : RectangularParameters} {f : ℝ→ℂ}
    {iL iR oL oR : ℂ} (hs : StationaryState p f)
    (hr : TwoSidedRadiation p f iL iR oL oR) :
    oL=p.layer.outgoingLeft iL iR ∧ oR=p.layer.outgoingRight iL iR := by
  obtain ⟨h1,h2⟩ := radiation_transfer_equations hs hr
  exact p.layer.solve_two_port iL iR oL oR h1 h2

/-- Entire-function uniqueness in the stated classical radiation class. -/
theorem scattering_state_unique {p : RectangularParameters} {f g : ℝ→ℂ}
    {iL iR fL fR gL gR : ℂ} (hf : StationaryState p f) (hg : StationaryState p g)
    (hrf : TwoSidedRadiation p f iL iR fL fR)
    (hrg : TwoSidedRadiation p g iL iR gL gR) : f=g := by
  obtain ⟨hfL,hfR⟩ := general_outgoing_amplitudes hf hrf
  obtain ⟨hgL,hgR⟩ := general_outgoing_amplitudes hg hrg
  have hL : fL=gL := hfL.trans hgL.symm
  have hR : fR=gR := hfR.trans hgR.symm
  obtain ⟨_,_,hfa,hfda⟩ := hrf.endpoint_traces hf
  obtain ⟨_,_,hga,hgda⟩ := hrg.endpoint_traces hg
  have hval : f p.width=g p.width := by rw [hfa,hga,hR]
  have hder : deriv f p.width=deriv g p.width := by rw [hfda,hgda,hR]
  have hin := p.profile.cauchy_unique_on_closed_interval p.width_pos
    ⟨le_of_lt p.width_pos,le_rfl⟩ f (deriv f) g (deriv g)
    hf.continuous hf.continuous_derivative hg.continuous hg.continuous_derivative
    (fun x _=>hf.hasDerivAt x) hf.interior_ode
    (fun x _=>hg.hasDerivAt x) hg.interior_ode hval hder
  funext x
  by_cases hx : x<0
  · rw [hrf.left x hx,hrg.left x hx,hL]
  · by_cases hxa : p.width<x
    · rw [hrf.right x hxa,hrg.right x hxa,hR]
    · exact (hin x ⟨le_of_not_gt hx,le_of_not_gt hxa⟩).1

/-- All regularity and radiation conditions, without an interior ansatz. -/
def AdmissibleScattering (p : RectangularParameters) (iL iR : ℂ) (f : ℝ→ℂ) : Prop :=
  StationaryState p f ∧ ∃ oL oR, TwoSidedRadiation p f iL iR oL oR

/-- Existence and uniqueness for every complex two-channel incoming vector. -/
theorem existsUnique_two_sided_state (p : RectangularParameters) (iL iR : ℂ) :
    ∃! f : ℝ→ℂ, AdmissibleScattering p iL iR f := by
  refine ⟨p.coherentWave iL iR, ?_, ?_⟩
  · exact ⟨p.coherentWave_stationary iL iR,
      p.layer.outgoingLeft iL iR,p.layer.outgoingRight iL iR,coherentWave_radiation p iL iR⟩
  · intro f hf
    obtain ⟨oL,oR,hr⟩ := hf.2
    exact scattering_state_unique hf.1 (p.coherentWave_stationary iL iR)
      hr (coherentWave_radiation p iL iR)

end QuantumTunneling
