/- API regression examples. Candidate source only; not evaluated by Lean yet.
Each geometry uses the SAME public theorem, with no specialized scattering proof. -/
import QuantumScattering
noncomputable section
namespace QuantumScattering.Examples
open QuantumScattering

def rectangle : PhysicalProblem where
  hbar := 1
  mass := 1
  energy := 1
  leftLevel := 0
  rightLevel := 0
  layers := [⟨2,1,by norm_num⟩]
  hbar_pos := by norm_num
  mass_pos := by norm_num
  left_open := by norm_num
  right_open := by norm_num

/-- A double barrier with a free middle interval. Multiple reflections are
included by matrix composition; probabilities are NOT multiplied layerwise. -/
def doubleBarrier : PhysicalProblem where
  hbar := 1
  mass := 1
  energy := 1
  leftLevel := 0
  rightLevel := 0
  layers := [⟨3,1/2,by norm_num⟩,⟨0,2,by norm_num⟩,⟨3,1/2,by norm_num⟩]
  hbar_pos := by norm_num
  mass_pos := by norm_num
  left_open := by norm_num
  right_open := by norm_num

/-- Negative well, evanescent segment, EXACT internal threshold and unequal leads. -/
def asymmetricMixed : PhysicalProblem where
  hbar := 1
  mass := 2
  energy := 3
  leftLevel := -1
  rightLevel := 1
  layers := [⟨-2,1,by norm_num⟩,⟨5,1/2,by norm_num⟩,
             ⟨3,2/3,by norm_num⟩,⟨0,3/4,by norm_num⟩]
  hbar_pos := by norm_num
  mass_pos := by norm_num
  left_open := by norm_num
  right_open := by norm_num

/-- Zero finite layers is allowed; different exterior levels produce a step. -/
def stepOnly : PhysicalProblem where
  hbar := 1
  mass := 1
  energy := 4
  leftLevel := 0
  rightLevel := 3
  layers := []
  hbar_pos := by norm_num
  mass_pos := by norm_num
  left_open := by norm_num
  right_open := by norm_num

example : FiniteScatteringCertificate rectangle := finite_piecewise_real_scattering rectangle
example : FiniteScatteringCertificate doubleBarrier := finite_piecewise_real_scattering doubleBarrier
example : FiniteScatteringCertificate asymmetricMixed := finite_piecewise_real_scattering asymmetricMixed
example : FiniteScatteringCertificate stepOnly := finite_piecewise_real_scattering stepOnly

example (iL iR : ℂ) : ∃! fv : (ℝ→ℂ)×(ℝ→ℂ),
    asymmetricMixed.problem.Admissible iL iR fv.1 fv.2 :=
  asymmetricMixed.problem.existsUnique_classical_scattering iL iR

example (xs ys : Stack) (y : State) :
    Stack.exitState (xs++ys) y=Stack.exitState ys (Stack.exitState xs y) :=
  (Stack.compositional_contract xs ys y).1

end QuantumScattering.Examples
