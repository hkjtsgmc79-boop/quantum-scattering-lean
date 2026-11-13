/- F1 candidate. Backend interface for spatially varying REAL coefficients.
This does not assert existence for every potential. A backend must supply two
ACTUAL normalized Cauchy solutions and their derivative proofs. Unit determinant,
flux conservation and channel unitarity are derived below, never input fields. -/
import QuantumScattering.LocalUniqueness

noncomputable section
namespace QuantumScattering

structure RealEvolution where
  coefficient : ℝ → ℝ
  a : ℝ → ℝ
  b : ℝ → ℝ
  c : ℝ → ℝ
  d : ℝ → ℝ
  a_zero : a 0=1
  b_zero : b 0=0
  c_zero : c 0=0
  d_zero : d 0=1
  a_deriv : ∀ x, HasDerivAt a (c x) x
  b_deriv : ∀ x, HasDerivAt b (d x) x
  c_deriv : ∀ x, HasDerivAt c (-coefficient x*a x) x
  d_deriv : ∀ x, HasDerivAt d (-coefficient x*b x) x

namespace RealEvolution

def wronskian (e : RealEvolution) (x : ℝ) : ℝ := e.a x*e.d x-e.b x*e.c x

lemma hasDerivAt_wronskian (e : RealEvolution) (x : ℝ) :
    HasDerivAt e.wronskian 0 x := by
  have h := ((e.a_deriv x).mul (e.d_deriv x)).sub ((e.b_deriv x).mul (e.c_deriv x))
  convert h using 1
  · rfl
  · ring

lemma wronskian_one (e : RealEvolution) (x : ℝ) : e.wronskian x=1 := by
  have hc : Continuous e.wronskian :=
    (show Differentiable ℝ e.wronskian from
      fun y => (e.hasDerivAt_wronskian y).differentiableAt).continuous
  have h := constant_on_Icc_of_deriv_zero
    (l:=min 0 x-1) (r:=max 0 x+1) (by
      have h0 := (min_le_max : min (0:ℝ) x ≤ max 0 x)
      linarith)
    hc (fun y _ => e.hasDerivAt_wronskian y)
    (x:=x) (y:=0)
    ⟨by have h0:=min_le_right (0:ℝ) x; linarith,
     by have h0:=le_max_right (0:ℝ) x; linarith⟩
    ⟨by have h0:=min_le_left (0:ℝ) x; linarith,
     by have h0:=le_max_left (0:ℝ) x; linarith⟩
  simpa [wronskian,e.a_zero,e.b_zero,e.c_zero,e.d_zero] using h

def transfer (e : RealEvolution) (x : ℝ) : RealTransfer :=
  ⟨e.a x,e.b x,e.c x,e.d x,e.wronskian_one x⟩

def flow (e : RealEvolution) (y : State) (x : ℝ) : State := (e.transfer x).act y

lemma hasDerivAt_value (e : RealEvolution) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (e.flow y t).value) (e.flow y x).slope x := by
  exact ((e.a_deriv x).ofReal_comp.mul_const y.value).add
    ((e.b_deriv x).ofReal_comp.mul_const y.slope)

lemma hasDerivAt_slope (e : RealEvolution) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (e.flow y t).slope)
      (-(e.coefficient x : ℂ)*(e.flow y x).value) x := by
  have h := ((e.c_deriv x).ofReal_comp.mul_const y.value).add
    ((e.d_deriv x).ofReal_comp.mul_const y.slope)
  convert h using 1
  · rfl
  · simp [flow, transfer, RealTransfer.act]
    ring

lemma actual_current (e : RealEvolution) (y : State) (hbar mass x : ℝ) :
    current hbar mass (fun t => (e.flow y t).value) x=(hbar/mass)*y.flux := by
  unfold current
  rw [(e.hasDerivAt_value y x).deriv]
  exact congrArg (fun u => (hbar/mass)*u) ((e.transfer x).flux_preserved y)

/-- The existing constant-potential backend is an actual instance of the
same variable-coefficient interface, not an unrelated parallel construction. -/
def ofLocal (P : LocalProfile) : RealEvolution where
  coefficient := fun _ => P.delta
  a := P.C
  b := P.S
  c := fun x => -P.delta*P.S x
  d := P.C
  a_zero := P.C_zero
  b_zero := P.S_zero
  c_zero := by simp [P.S_zero]
  d_zero := P.C_zero
  a_deriv := P.C_deriv
  b_deriv := P.S_deriv
  c_deriv := fun x => (P.S_deriv x).const_mul (-P.delta)
  d_deriv := P.C_deriv

lemma ofLocal_transfer (P : LocalProfile) (x : ℝ) : (ofLocal P).transfer x=P.transfer x := by
  ext <;> rfl

/-- Generic algebraic closure for any future verified evolution backend.
The premise is differential data, not pre-assumed current or S unitarity. -/
theorem scattering_contract (e : RealEvolution) (x : ℝ) (left right : Port) :
    let M := channelTransfer left right (e.transfer x)
    M.scatteringMatrix.conjTranspose*M.scatteringMatrix=1 ∧
    (∀ iL iR, ∃! o : ℂ × ℂ, M.act ⟨iL,o.1⟩=⟨o.2,iR⟩) := by
  exact ⟨(channelTransfer left right (e.transfer x)).unitary_matrix.1,
    (channelTransfer left right (e.transfer x)).existsUnique_outgoing⟩

end RealEvolution
end QuantumScattering
