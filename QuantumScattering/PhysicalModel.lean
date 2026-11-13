/- F1 candidate. Construct the spectral model from physical data.
Real heights can be negative. Exterior levels can differ. Both exterior
channels must be open. Mass is constant throughout the system. -/
import QuantumScattering.FiniteScattering

noncomputable section
namespace QuantumScattering

structure PhysicalLayer where
  height : ℝ
  width : ℝ
  width_pos : 0 < width

structure PhysicalProblem where
  hbar : ℝ
  mass : ℝ
  energy : ℝ
  leftLevel : ℝ
  rightLevel : ℝ
  layers : List PhysicalLayer
  hbar_pos : 0 < hbar
  mass_pos : 0 < mass
  left_open : leftLevel < energy
  right_open : rightLevel < energy

namespace PhysicalProblem

def delta (p : PhysicalProblem) (V : ℝ) : ℝ := 2*p.mass*(p.energy-V)/p.hbar^2

def k (p : PhysicalProblem) (V : ℝ) : ℝ := Real.sqrt (p.delta V)

lemma k_pos (p : PhysicalProblem) (V : ℝ) (hV : V<p.energy) : 0<p.k V := by
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr hV))
    (pow_pos p.hbar_pos 2)

lemma k_sq (p : PhysicalProblem) (V : ℝ) (hV : V<p.energy) : p.k V^2=p.delta V := by
  apply Real.sq_sqrt
  exact le_of_lt (div_pos (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr hV))
    (pow_pos p.hbar_pos 2))

def layer (p : PhysicalProblem) (s : PhysicalLayer) : Layer :=
  ⟨p.delta s.height,s.width,s.width_pos⟩

def problem (p : PhysicalProblem) : Problem where
  left := ⟨p.k p.leftLevel,p.k_pos p.leftLevel p.left_open⟩
  right := ⟨p.k p.rightLevel,p.k_pos p.rightLevel p.right_open⟩
  layers := p.layers.map p.layer

def tailPotential (rightLevel : ℝ) : List PhysicalLayer → ℝ → ℝ
  | [],_ => rightLevel
  | s::rest,x => if x<s.width then s.height else tailPotential rightLevel rest (x-s.width)

def potential (p : PhysicalProblem) (x : ℝ) : ℝ :=
  if x<0 then p.leftLevel else tailPotential p.rightLevel p.layers x

lemma tailCoefficient_eq (p : PhysicalProblem) (xs : List PhysicalLayer) (x : ℝ) :
    Stack.tailCoefficient p.problem.right (xs.map p.layer) x=
      p.delta (tailPotential p.rightLevel xs x) := by
  induction xs generalizing x with
  | nil => exact p.k_sq p.rightLevel p.right_open
  | cons s rest ih =>
    by_cases h : x<s.width
    · simp [Stack.tailCoefficient,tailPotential,layer,h]
    · simp [Stack.tailCoefficient,tailPotential,layer,h,ih]

lemma coefficient_eq (p : PhysicalProblem) (x : ℝ) :
    p.problem.coefficient x=p.delta (p.potential x) := by
  by_cases h : x<0
  · simpa [Problem.coefficient,Stack.coefficient,problem,potential,h] using
      p.k_sq p.leftLevel p.left_open
  · simpa [Problem.coefficient,Stack.coefficient,problem,potential,h] using
      p.tailCoefficient_eq p.layers x

lemma kinetic_delta (p : PhysicalProblem) (V : ℝ) :
    p.hbar^2/(2*p.mass)*p.delta V=p.energy-V := by
  unfold delta
  field_simp [ne_of_gt p.hbar_pos,ne_of_gt p.mass_pos] <;> ring

/-- Literal physical equation for arbitrary finite real layers, including any
number of exact interior thresholds. No solution is an input field. -/
theorem schrodinger (p : PhysicalProblem) (iL iR : ℂ) (x : ℝ)
    (hx : x∉p.problem.jumps) :
    -(p.hbar^2/(2*p.mass) : ℝ) • deriv (deriv (p.problem.wave iL iR)) x +
      p.potential x • p.problem.wave iL iR x =
      p.energy • p.problem.wave iL iR x := by
  rw [p.problem.second_order iL iR x hx,p.coefficient_eq]
  have hc : ((p.hbar^2/(2*p.mass) : ℝ) : ℂ)*(p.delta (p.potential x) : ℂ)=
      (p.energy : ℂ)-(p.potential x : ℂ) := by exact_mod_cast p.kinetic_delta (p.potential x)
  simp only [Complex.real_smul, Complex.ofReal_neg]
  linear_combination (p.problem.wave iL iR x)*hc

theorem full_physical_existence (p : PhysicalProblem) (iL iR : ℂ) :
    ContDiff ℝ 1 (p.problem.wave iL iR) ∧
    (∀ x, x∉p.problem.jumps →
      -(p.hbar^2/(2*p.mass) : ℝ) • deriv (deriv (p.problem.wave iL iR)) x +
      p.potential x • p.problem.wave iL iR x =
      p.energy • p.problem.wave iL iR x) ∧
    p.problem.channels.scatteringMatrix.conjTranspose*p.problem.channels.scatteringMatrix=1 :=
  ⟨p.problem.C1 iL iR,p.schrodinger iL iR,p.problem.channels.unitary_matrix.1⟩

end PhysicalProblem
end QuantumScattering
