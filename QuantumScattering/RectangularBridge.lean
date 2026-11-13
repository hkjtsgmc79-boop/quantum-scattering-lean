/-
F2: exact regression bridge to the unmodified Q5 rectangular project.
The Q5 namespace is vendored with source hashes, NOT regarded as pre-verified.
The new framework uses unit-flux channels; Q5 uses unit wave amplitude.
Thus old inputs (a,b) correspond to new inputs (sqrt(k)*a,sqrt(k)*b).
This file proves equality of actual functions, slopes, currents and S entries,
not just agreement of one transmission probability. Uncompiled candidates.
-/
import QuantumScattering.Radiation
import QuantumTunneling.BidirectionalProject

noncomputable section
namespace QuantumScattering
namespace RectangularBridge

abbrev Old := QuantumTunneling.RectangularParameters

def model (p : Old) : PhysicalProblem where
  hbar := p.hbar
  mass := p.mass
  energy := p.energy
  leftLevel := 0
  rightLevel := 0
  layers := [⟨p.height,p.width,p.width_pos⟩]
  hbar_pos := p.hbar_pos
  mass_pos := p.mass_pos
  left_open := p.energy_pos
  right_open := p.energy_pos

def root (p : Old) : ℝ := (model p).problem.left.root

lemma root_pos (p : Old) : 0<root p := (model p).problem.left.root_pos
lemma root_ne_zero (p : Old) : (root p : ℂ)≠0 := by exact_mod_cast ne_of_gt (root_pos p)

lemma right_eq_left (p : Old) : (model p).problem.right=(model p).problem.left := rfl

lemma port_k (p : Old) : (model p).problem.left.k=p.k := by
  have ha := (model p).k_sq 0 p.energy_pos
  have hb := p.k_sq
  have hp := (model p).k_pos 0 p.energy_pos
  change (model p).k 0 = p.k
  change (model p).k 0 ^ 2 = 2 * p.mass * (p.energy - 0) / p.hbar ^ 2 at ha
  rw [sub_zero, ← hb] at ha
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp ha).resolve_right (by linarith [p.k_pos])

lemma total_width (p : Old) : Stack.width (model p).problem.layers=p.width := by
  simp [model,PhysicalProblem.problem,PhysicalProblem.layer,Stack.width]

lemma jump_iff (p : Old) (x : ℝ) :
    x∈(model p).problem.jumps ↔ x=0 ∨ x=p.width := by
  simp [Problem.jumps,Stack.jumps,Stack.tailJumps,model,
    PhysicalProblem.problem,PhysicalProblem.layer]

/-- Coefficients agree literally, including the chosen interface convention.
Potential endpoint VALUES may differ, but are not used at excluded jumps. -/
lemma coefficient_eq (p : Old) (x : ℝ) :
    (model p).problem.coefficient x= -p.layer.odeCoefficient x := by
  have hk := port_k p
  have hd := p.profile_delta
  change (if x<0 then (model p).problem.left.k^2 else
    if x<p.width then 2*p.mass*(p.energy-p.height)/p.hbar^2
    else (model p).problem.right.k^2)=_
  rw [right_eq_left,port_k,← hd]
  simp only [QuantumTunneling.ScatteringLayer.odeCoefficient,
    QuantumTunneling.RectangularParameters.layer]
  by_cases h0 : x < 0 <;> by_cases hw : x < p.width <;> simp [h0, hw]

lemma plane_eq (k x : ℝ) : plane k x=QuantumTunneling.plane k x := rfl
lemma absSq_eq (z : ℂ) : absSq z=QuantumTunneling.absSq z := rfl
lemma current_eq (h m : ℝ) (f : ℝ→ℂ) (x : ℝ) :
    current h m f x=QuantumTunneling.current h m f x := rfl

/-- Canonical new wave evaluated at the physically identical raw-amplitude input. -/
def rawWave (p : Old) (a b : ℂ) : ℝ→ℂ :=
  (model p).problem.wave ((root p:ℂ)*a) ((root p:ℂ)*b)

def rawOutputs (p : Old) (a b : ℂ) : ℂ × ℂ :=
  let o := (model p).problem.outgoing ((root p:ℂ)*a) ((root p:ℂ)*b)
  (o.1/(root p:ℂ),o.2/(root p:ℂ))

lemma rawWave_stationary (p : Old) (a b : ℂ) :
    QuantumTunneling.StationaryState p (rawWave p a b) := by
  have h := (model p).problem.classical ((root p:ℂ)*a) ((root p:ℂ)*b)
  refine ⟨h.C1,?_⟩
  intro x h0 hw
  have hx : x∉(model p).problem.jumps := by
    rw [jump_iff]
    exact not_or.mpr ⟨h0,hw⟩
  have he := h.equation x hx
  rw [coefficient_eq] at he
  simpa only [rawWave,← h.deriv_eq,Complex.ofReal_neg,neg_neg,
    Complex.real_smul] using he

lemma rawWave_radiation (p : Old) (a b : ℂ) :
    QuantumTunneling.TwoSidedRadiation p (rawWave p a b) a b
      (rawOutputs p a b).1 (rawOutputs p a b).2 := by
  constructor
  · intro x hx
    have he := (model p).problem.left_plane_wave ((root p:ℂ)*a) ((root p:ℂ)*b) x hx
    change rawWave p a b x=_ at he
    rw [he,port_k]
    simp only [plane_eq, QuantumTunneling.freeWave, rawOutputs]
    change _ / (root p : ℂ) = _
    field_simp [root_ne_zero p] <;> ring
  · intro x hx
    have he := (model p).problem.right_plane_wave ((root p:ℂ)*a) ((root p:ℂ)*b) x
      (by rw [total_width]; exact le_of_lt hx)
    change rawWave p a b x=_ at he
    rw [he,right_eq_left,port_k,total_width]
    simp only [plane_eq, QuantumTunneling.freeWave, rawOutputs]
    change _ / (root p : ℂ) = _
    field_simp [root_ne_zero p] <;> ring

/-- Reuse general function uniqueness: no new elementary-profile equality is
assumed, and no fundamental-solution ansatz is added to the input. -/
theorem wave_eq_legacy (p : Old) (a b : ℂ) :
    rawWave p a b=p.coherentWave a b := by
  obtain ⟨f,hf,hu⟩ := QuantumTunneling.existsUnique_two_sided_state p a b
  have hnew : QuantumTunneling.AdmissibleScattering p a b (rawWave p a b) :=
    ⟨rawWave_stationary p a b,(rawOutputs p a b).1,(rawOutputs p a b).2,
      rawWave_radiation p a b⟩
  have hold : QuantumTunneling.AdmissibleScattering p a b (p.coherentWave a b) :=
    ⟨p.coherentWave_stationary a b,p.layer.outgoingLeft a b,p.layer.outgoingRight a b,
      QuantumTunneling.coherentWave_radiation p a b⟩
  exact (hu _ hnew).trans (hu _ hold).symm

theorem derivative_eq_legacy (p : Old) (a b : ℂ) :
    deriv (rawWave p a b)=deriv (p.coherentWave a b) := by rw [wave_eq_legacy]

theorem current_eq_legacy (p : Old) (a b : ℂ) (x : ℝ) :
    current p.hbar p.mass (rawWave p a b) x=
      QuantumTunneling.current p.hbar p.mass (p.coherentWave a b) x := by
  rw [wave_eq_legacy,current_eq]

/-- Boundary equations connect the actual outgoing coefficients, including phases. -/
theorem rawOutputs_eq_legacy (p : Old) (a b : ℂ) :
    rawOutputs p a b=(p.layer.outgoingLeft a b,p.layer.outgoingRight a b) := by
  obtain ⟨h1,h2⟩ := QuantumTunneling.radiation_transfer_equations
    (rawWave_stationary p a b) (rawWave_radiation p a b)
  obtain ⟨hl,hr⟩ := p.layer.solve_two_port a b _ _ h1 h2
  exact Prod.ext hl hr

lemma rawOutputs_unit_left (p : Old) :
    rawOutputs p 1 0=((model p).problem.channels.rLeft,(model p).problem.channels.t) := by
  unfold rawOutputs Problem.outgoing ChannelTransfer.outgoing
  apply Prod.ext <;> simp only [mul_one,mul_zero,add_zero] <;>
    field_simp [root_ne_zero p] <;> ring

lemma rawOutputs_unit_right (p : Old) :
    rawOutputs p 0 1=((model p).problem.channels.t,(model p).problem.channels.rRight) := by
  unfold rawOutputs Problem.outgoing ChannelTransfer.outgoing
  apply Prod.ext <;> simp only [mul_one,mul_zero,zero_add] <;>
    field_simp [root_ne_zero p] <;> ring

lemma amplitudes_eq_legacy (p : Old) :
    (model p).problem.channels.rLeft=p.reflectionAmplitude ∧
    (model p).problem.channels.t=p.transmissionAmplitude ∧
    (model p).problem.channels.rRight=p.reflectionAmplitude := by
  have hl := rawOutputs_eq_legacy p 1 0
  have hr := rawOutputs_eq_legacy p 0 1
  rw [rawOutputs_unit_left] at hl
  rw [rawOutputs_unit_right] at hr
  refine ⟨?_,?_,?_⟩
  · simpa [QuantumTunneling.ScatteringLayer.outgoingLeft,
      QuantumTunneling.RectangularParameters.reflectionAmplitude] using congrArg Prod.fst hl
  · simpa [QuantumTunneling.ScatteringLayer.outgoingRight,
      QuantumTunneling.RectangularParameters.transmissionAmplitude] using congrArg Prod.snd hl
  · simpa [QuantumTunneling.ScatteringLayer.outgoingRight,
      QuantumTunneling.RectangularParameters.reflectionAmplitude] using congrArg Prod.snd hr

theorem scatteringMatrix_eq_legacy (p : Old) :
    (model p).problem.channels.scatteringMatrix=p.layer.scatteringMatrix := by
  obtain ⟨hl,ht,hr⟩ := amplitudes_eq_legacy p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChannelTransfer.scatteringMatrix,QuantumTunneling.ScatteringLayer.scatteringMatrix,
      hl,ht,hr,QuantumTunneling.RectangularParameters.reflectionAmplitude,
      QuantumTunneling.RectangularParameters.transmissionAmplitude]

theorem transmission_eq_legacy (p : Old) :
    (model p).problem.channels.transmission=p.layer.T := by
  unfold ChannelTransfer.transmission
  rw [(amplitudes_eq_legacy p).2.1,absSq_eq]
  rfl

theorem reflection_eq_legacy (p : Old) :
    (model p).problem.channels.reflectionLeft=p.layer.R ∧
    (model p).problem.channels.reflectionRight=p.layer.R := by
  obtain ⟨hl,ht,hr⟩ := amplitudes_eq_legacy p
  constructor
  · unfold ChannelTransfer.reflectionLeft
    rw [hl,absSq_eq]
    rfl
  · unfold ChannelTransfer.reflectionRight
    rw [hr,absSq_eq]
    rfl

/-- Q5 resonance classification is now a theorem about the new framework. -/
theorem framework_complete_resonance (p : Old) :
    (model p).problem.channels.transmission=1 ↔ p.height<p.energy ∧
      ∃! n:ℕ, p.width=QuantumTunneling.resonantWidth p.q n := by
  rw [transmission_eq_legacy]
  exact p.complete_resonance_classification

/-- All-energy scalar and complex-matrix family bridges for reuse of Q5
threshold continuity and physical limits. No multi-layer generalization is claimed. -/
theorem framework_physical_families (p : Old) :
    (model p).problem.channels.transmission=
      QuantumTunneling.transmissionFunction p.hbar p.mass p.height p.width p.energy ∧
    (model p).problem.channels.scatteringMatrix=
      QuantumTunneling.energyScatteringMatrix p.hbar p.mass p.height p.width p.energy := by
  have h := QuantumTunneling.rectangular_barrier_bidirectional_project p
  exact ⟨(transmission_eq_legacy p).trans h.physical_scalar_bridge,
    (scatteringMatrix_eq_legacy p).trans h.physical_matrix_bridge⟩

end RectangularBridge
end QuantumScattering
