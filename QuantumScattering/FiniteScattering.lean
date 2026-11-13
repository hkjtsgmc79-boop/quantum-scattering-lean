/- F1 candidate. Full explicit finite-stack wave linked to the same channel
transfer used for the scattering amplitudes. No probability ratio is defined
independently of the actual current or the state differential equation. -/
import QuantumScattering.StackWave

noncomputable section
namespace QuantumScattering

structure Problem where
  left : Port
  right : Port
  layers : Stack

namespace Problem

def transfer (p : Problem) : RealTransfer := Stack.transfer p.layers
def channels (p : Problem) : ChannelTransfer := channelTransfer p.left p.right p.transfer

def outgoing (p : Problem) (iL iR : ℂ) : ℂ × ℂ := p.channels.outgoing iL iR

def initial (p : Problem) (iL iR : ℂ) : State :=
  p.left.encode ⟨iL,(p.outgoing iL iR).1⟩

def state (p : Problem) (iL iR : ℂ) (x : ℝ) : State :=
  Stack.waveState p.left p.right p.layers (p.initial iL iR) x

def wave (p : Problem) (iL iR : ℂ) (x : ℝ) : ℂ := (p.state iL iR x).value
def waveD (p : Problem) (iL iR : ℂ) (x : ℝ) : ℂ := (p.state iL iR x).slope

def coefficient (p : Problem) : ℝ → ℝ := Stack.coefficient p.left p.right p.layers

def jumps (p : Problem) : Set ℝ := Stack.jumps p.layers

theorem classical (p : Problem) (iL iR : ℂ) :
    ClassicalState p.coefficient p.jumps (p.wave iL iR) (p.waveD iL iR) :=
  Stack.classical_wave p.left p.right p.layers (p.initial iL iR)

theorem C1 (p : Problem) (iL iR : ℂ) : ContDiff ℝ 1 (p.wave iL iR) :=
  (p.classical iL iR).C1

theorem second_order (p : Problem) (iL iR : ℂ) (x : ℝ) (hx : x∉p.jumps) :
    deriv (deriv (p.wave iL iR)) x=-(p.coefficient x : ℂ)*p.wave iL iR x :=
  (p.classical iL iR).second_order x hx

lemma exit_data (p : Problem) (iL iR : ℂ) :
    p.transfer.act (p.initial iL iR)=p.right.encode ⟨(p.outgoing iL iR).2,iR⟩ := by
  have h := channelTransfer_action p.left p.right p.transfer ⟨iL,(p.outgoing iL iR).1⟩
  change p.right.encode (p.channels.act ⟨iL,(p.outgoing iL iR).1⟩)=
    p.transfer.act (p.initial iL iR) at h
  simpa only [outgoing, p.channels.outgoing_solves] using h.symm

lemma left_boundary (p : Problem) (iL iR : ℂ) :
    p.left.decode (p.state iL iR 0)=⟨iL,(p.outgoing iL iR).1⟩ := by
  simp [state,initial]

lemma right_boundary (p : Problem) (iL iR : ℂ) :
    p.right.decode (p.state iL iR (Stack.width p.layers))=
      ⟨(p.outgoing iL iR).2,iR⟩ := by
  rw [state,Stack.waveState_exit]
  change p.right.decode (p.transfer.act (p.initial iL iR))=_
  rw [p.exit_data,p.right.decode_encode]

lemma left_exterior (p : Problem) (iL iR : ℂ) (x : ℝ) (hx : x<0) :
    p.state iL iR x=p.left.profile.flow (p.initial iL iR) x := by
  simp only [state,Stack.waveState,if_pos hx]

lemma right_exterior (p : Problem) (iL iR : ℂ) (x : ℝ)
    (hx : Stack.width p.layers ≤ x) :
    p.state iL iR x=p.right.profile.flow
      (p.right.encode ⟨(p.outgoing iL iR).2,iR⟩) (x-Stack.width p.layers) := by
  have h0 : 0≤x := le_trans (Stack.width_nonneg _) hx
  rw [state,Stack.waveState,if_neg (not_lt.mpr h0),Stack.tail_right _ _ _ _ hx]
  change p.right.profile.flow (p.transfer.act (p.initial iL iR)) _=_
  rw [p.exit_data]

theorem current_left (p : Problem) (iL iR : ℂ) (hbar mass x : ℝ) :
    current hbar mass (p.wave iL iR) x=
      (hbar/mass)*(absSq iL-absSq (p.outgoing iL iR).1) := by
  change current hbar mass (fun t => (p.state iL iR t).value) x = _
  change current hbar mass
    (fun t => (Stack.waveState p.left p.right p.layers (p.initial iL iR) t).value) x = _
  rw [Stack.actual_current]
  unfold initial
  rw [p.left.encode_flux]
  rfl

theorem current_right (p : Problem) (iL iR : ℂ) (hbar mass x : ℝ) :
    current hbar mass (p.wave iL iR) x=
      (hbar/mass)*(absSq (p.outgoing iL iR).2-absSq iR) := by
  rw [p.current_left]
  have h := p.channels.coherent_balance iL iR
  change absSq (p.outgoing iL iR).1+absSq (p.outgoing iL iR).2=absSq iL+absSq iR at h
  congr 1
  linarith

/-- Unlike a hard-coded barrier theorem, this has arbitrary list length and
independent positive left/right wave numbers. -/
theorem finite_stack_scattering (p : Problem) (iL iR : ℂ) :
    ClassicalState p.coefficient p.jumps (p.wave iL iR) (p.waveD iL iR) ∧
    ContDiff ℝ 1 (p.wave iL iR) ∧
    p.left.decode (p.state iL iR 0)=⟨iL,(p.outgoing iL iR).1⟩ ∧
    p.right.decode (p.state iL iR (Stack.width p.layers))=⟨(p.outgoing iL iR).2,iR⟩ ∧
    (∀ hbar mass x, current hbar mass (p.wave iL iR) x=
      (hbar/mass)*(absSq iL-absSq (p.outgoing iL iR).1)) ∧
    p.channels.scatteringMatrix.conjTranspose*p.channels.scatteringMatrix=1 ∧
    p.channels.scatteringMatrix*p.channels.scatteringMatrix.conjTranspose=1 ∧
    p.channels.scatteringMatrix.transpose=p.channels.scatteringMatrix := by
  exact ⟨p.classical iL iR,p.C1 iL iR,p.left_boundary iL iR,p.right_boundary iL iR,
    p.current_left iL iR,p.channels.unitary_matrix.1,p.channels.unitary_matrix.2,
    p.channels.symmetric_matrix⟩

end Problem
end QuantumScattering
