/- F1 candidate. Finite REAL layers: no nonnegativity hypothesis on heights. -/
import QuantumScattering.LocalFlow

noncomputable section
namespace QuantumScattering

/-- A spectral segment. A signed delta represents oscillatory, linear or
exponential behavior without restricting the incident energy relative to V. -/
structure Layer where
  delta : ℝ
  width : ℝ
  width_pos : 0 < width

namespace Layer

def profile (s : Layer) : LocalProfile := LocalProfile.ofDelta s.delta

def transfer (s : Layer) : RealTransfer := s.profile.transfer s.width

def flow (s : Layer) (y : State) (x : ℝ) : State := s.profile.flow y x

@[simp] lemma delta_profile (s : Layer) : s.profile.delta=s.delta :=
  LocalProfile.ofDelta_delta s.delta
@[simp] lemma flow_zero (s : Layer) (y : State) : s.flow y 0=y :=
  s.profile.flow_zero y
lemma endpoint (s : Layer) (y : State) : s.flow y s.width=s.transfer.act y := rfl
lemma hasDerivAt_value (s : Layer) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (s.flow y t).value) (s.flow y x).slope x :=
  s.profile.hasDerivAt_value y x
lemma hasDerivAt_slope (s : Layer) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (s.flow y t).slope) (-(s.delta : ℂ)*(s.flow y x).value) x := by
  simpa only [flow, delta_profile] using s.profile.hasDerivAt_slope y x
lemma flux_preserved (s : Layer) (y : State) (x : ℝ) :
    (s.flow y x).flux=y.flux := s.profile.flux_preserved y x
end Layer

abbrev Stack := List Layer

namespace Stack

def width : Stack → ℝ
  | [] => 0
  | s::rest => s.width+width rest

def transfer : Stack → RealTransfer
  | [] => RealTransfer.identity
  | s::rest => (transfer rest).after s.transfer

def exitState : Stack → State → State
  | [],y => y
  | s::rest,y => exitState rest (s.transfer.act y)

lemma width_nonneg (xs : Stack) : 0 ≤ width xs := by
  induction xs with
  | nil => simp [width]
  | cons s rest ih => exact add_nonneg (le_of_lt s.width_pos) ih

lemma width_append (xs ys : Stack) : width (xs++ys)=width xs+width ys := by
  induction xs with
  | nil => simp [width]
  | cons s rest ih => simp [width,ih,add_assoc]

lemma transfer_append (xs ys : Stack) :
    transfer (xs++ys)=(transfer ys).after (transfer xs) := by
  induction xs with
  | nil => simp [transfer]
  | cons s rest ih => simp [transfer,ih,RealTransfer.after_assoc]

lemma exitState_eq_transfer (xs : Stack) (y : State) :
    exitState xs y=(transfer xs).act y := by
  induction xs generalizing y with
  | nil => simp [exitState,transfer]
  | cons s rest ih => simp [exitState,transfer,ih,RealTransfer.after_act]

theorem exit_flux (xs : Stack) (y : State) : (exitState xs y).flux=y.flux := by
  rw [exitState_eq_transfer]
  exact (transfer xs).flux_preserved y

/-- New blocks compose by proof reuse, not re-solving all previous coefficients. -/
theorem compositional_contract (xs ys : Stack) (y : State) :
    exitState (xs++ys) y = exitState ys (exitState xs y) ∧
    (exitState (xs++ys) y).flux=y.flux := by
  constructor
  · simp only [exitState_eq_transfer,transfer_append,RealTransfer.after_act]
  · exact exit_flux _ _

end Stack
end QuantumScattering
