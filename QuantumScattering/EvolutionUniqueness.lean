/- F2: completeness and uniqueness for a verified variable-coefficient backend.
The coefficient need not be piecewise constant. Actual fundamental solutions
and their derivatives are the backend's contract, not scattering conclusions.
Uncompiled proof candidates. -/
import QuantumScattering.EvolutionInterface

noncomputable section
open Set
namespace QuantumScattering
namespace RealEvolution

@[simp] lemma transfer_zero (e : RealEvolution) : e.transfer 0=RealTransfer.identity := by
  ext <;> simp [transfer,RealTransfer.identity,e.a_zero,e.b_zero,e.c_zero,e.d_zero]
@[simp] lemma flow_zero (e : RealEvolution) (y : State) : e.flow y 0=y := by simp [flow]

lemma continuous_a (e : RealEvolution) : Continuous e.a :=
  (show Differentiable ℝ e.a from fun x=>(e.a_deriv x).differentiableAt).continuous
lemma continuous_b (e : RealEvolution) : Continuous e.b :=
  (show Differentiable ℝ e.b from fun x=>(e.b_deriv x).differentiableAt).continuous
lemma continuous_c (e : RealEvolution) : Continuous e.c :=
  (show Differentiable ℝ e.c from fun x=>(e.c_deriv x).differentiableAt).continuous
lemma continuous_d (e : RealEvolution) : Continuous e.d :=
  (show Differentiable ℝ e.d from fun x=>(e.d_deriv x).differentiableAt).continuous
lemma continuous_value (e : RealEvolution) (y : State) :
    Continuous (fun x=>(e.flow y x).value) :=
  (show Differentiable ℝ (fun x=>(e.flow y x).value) from
    fun x=>(e.hasDerivAt_value y x).differentiableAt).continuous
lemma continuous_slope (e : RealEvolution) (y : State) :
    Continuous (fun x=>(e.flow y x).slope) :=
  (show Differentiable ℝ (fun x=>(e.flow y x).slope) from
    fun x=>(e.hasDerivAt_slope y x).differentiableAt).continuous

def firstCoefficient (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ) : ℂ :=
  (e.d x:ℂ)*f x-(e.b x:ℂ)*v x

def secondCoefficient (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ) : ℂ :=
  -(e.c x:ℂ)*f x+(e.a x:ℂ)*v x

lemma coefficient_derivatives_zero (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ)
    (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-(e.coefficient x:ℂ)*f x) x) :
    HasDerivAt (e.firstCoefficient f v) 0 x ∧
    HasDerivAt (e.secondCoefficient f v) 0 x := by
  constructor
  · have h := ((e.d_deriv x).ofReal_comp.mul hf).sub ((e.b_deriv x).ofReal_comp.mul hv)
    convert h using 1
    · rfl
    · simp [Complex.ofReal_mul]
      ring
  · have h := ((e.c_deriv x).ofReal_comp.neg.mul hf).add ((e.a_deriv x).ofReal_comp.mul hv)
    convert h using 1
    · rfl
    · simp [Complex.ofReal_mul]
      ring

lemma reconstruct (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ) :
    (e.transfer x).act ⟨e.firstCoefficient f v x,e.secondCoefficient f v x⟩=
      (⟨f x,v x⟩:State) := by
  have h : (e.a x:ℂ)*(e.d x:ℂ)-(e.b x:ℂ)*(e.c x:ℂ)=1 := by
    have hw : e.a x*e.d x-e.b x*e.c x=1 := e.wronskian_one x
    exact_mod_cast hw
  apply State.ext
  · dsimp [transfer,RealTransfer.act,firstCoefficient,secondCoefficient]
    linear_combination (f x)*h
  · dsimp [transfer,RealTransfer.act,firstCoefficient,secondCoefficient]
    linear_combination (v x)*h

/-- Every classical solution in the finite segment is represented by its actual
left endpoint data. No guessed wave ansatz is part of the hypotheses. -/
theorem state_representation (e : RealEvolution) {L : ℝ} (hL : 0<L)
    (f v : ℝ→ℂ) (hf : Continuous f) (hv : Continuous v)
    (hfv : ∀ x∈Ioo 0 L, HasDerivAt f (v x) x)
    (hode : ∀ x∈Ioo 0 L, HasDerivAt v (-(e.coefficient x:ℂ)*f x) x)
    (x : ℝ) (hx : x∈Icc 0 L) :
    (⟨f x,v x⟩:State)=e.flow ⟨f 0,v 0⟩ x := by
  have hc1 : Continuous (e.firstCoefficient f v) :=
    ((Complex.continuous_ofReal.comp e.continuous_d).mul hf).sub
      ((Complex.continuous_ofReal.comp e.continuous_b).mul hv)
  have hc2 : Continuous (e.secondCoefficient f v) :=
    ((Complex.continuous_ofReal.comp e.continuous_c).neg.mul hf).add
      ((Complex.continuous_ofReal.comp e.continuous_a).mul hv)
  have h1 := constant_on_Icc_of_deriv_zero hL hc1
    (fun y hy => (e.coefficient_derivatives_zero f v y (hfv y hy) (hode y hy)).1)
    hx (show (0:ℝ)∈Icc 0 L from ⟨le_rfl,le_of_lt hL⟩)
  have h2 := constant_on_Icc_of_deriv_zero hL hc2
    (fun y hy => (e.coefficient_derivatives_zero f v y (hfv y hy) (hode y hy)).2)
    hx (show (0:ℝ)∈Icc 0 L from ⟨le_rfl,le_of_lt hL⟩)
  have h10 : e.firstCoefficient f v 0=f 0 := by
    simp [firstCoefficient,e.d_zero,e.b_zero]
  have h20 : e.secondCoefficient f v 0=v 0 := by
    simp [secondCoefficient,e.c_zero,e.a_zero]
  rw [h10] at h1
  rw [h20] at h2
  simpa [flow,h1,h2] using (e.reconstruct f v x).symm

end RealEvolution
end QuantumScattering
