/- F2: constant-medium propagation forms a spatial one-parameter group.
The addition law is derived from actual ODE uniqueness, not postulated.
All source in this file is an uncompiled proof candidate. -/
import QuantumScattering.LocalUniqueness

noncomputable section
open Set
namespace QuantumScattering
namespace LocalProfile

/-- Global representation from initial data at zero, using a sufficiently large
closed interval; the ODE still refers to actual derivatives. -/
lemma global_representation (P : LocalProfile) (f v : ℝ→ℂ)
    (hf : ∀ x, HasDerivAt f (v x) x)
    (hv : ∀ x, HasDerivAt v (-(P.delta:ℂ)*f x) x) (x : ℝ) :
    (⟨f x,v x⟩ : State)=P.flow ⟨f 0,v 0⟩ x := by
  have hfc : Continuous f :=
    (show Differentiable ℝ f from fun t => (hf t).differentiableAt).continuous
  have hvc : Continuous v :=
    (show Differentiable ℝ v from fun t => (hv t).differentiableAt).continuous
  have hlr : min 0 x-1<max 0 x+1 := by
    have h := (min_le_max : min (0:ℝ) x ≤ max 0 x)
    linarith
  have h0 : (0:ℝ)∈Icc (min 0 x-1) (max 0 x+1) :=
    ⟨by have h:=min_le_left (0:ℝ) x; linarith,
     by have h:=le_max_left (0:ℝ) x; linarith⟩
  have hx : x∈Icc (min 0 x-1) (max 0 x+1) :=
    ⟨by have h:=min_le_right (0:ℝ) x; linarith,
     by have h:=le_max_right (0:ℝ) x; linarith⟩
  obtain ⟨h1,h2⟩ := P.representation_on_closed_interval hlr h0 f v hfc hvc
    (fun t _=>hf t) (by intro t _; simpa [Complex.real_smul] using hv t) x hx
  apply State.ext
  · simpa [flow,transfer,RealTransfer.act,mul_comm] using h1
  · simpa [flow,transfer,RealTransfer.act,mul_comm,mul_left_comm,mul_assoc] using h2

lemma flow_add (P : LocalProfile) (y : State) (s t : ℝ) :
    P.flow y (s+t)=P.flow (P.flow y s) t := by
  have h := P.global_representation
    (fun x => (P.flow y (s+x)).value)
    (fun x => (P.flow y (s+x)).slope)
    (by
      intro x
      simpa [Function.comp_def] using
        (P.hasDerivAt_value y (s+x)).scomp x ((hasDerivAt_id x).const_add s))
    (by
      intro x
      simpa [Function.comp_def] using
        (P.hasDerivAt_slope y (s+x)).scomp x ((hasDerivAt_id x).const_add s)) t
  simpa using h
end LocalProfile

namespace RealTransfer
lemma ext_of_action {P Q : RealTransfer} (h : ∀ y, P.act y=Q.act y) : P=Q := by
  have ha := congrArg State.value (h ⟨1,0⟩)
  have hc := congrArg State.slope (h ⟨1,0⟩)
  have hb := congrArg State.value (h ⟨0,1⟩)
  have hd := congrArg State.slope (h ⟨0,1⟩)
  apply RealTransfer.ext
  · simpa [act] using ha
  · simpa [act] using hb
  · simpa [act] using hc
  · simpa [act] using hd
end RealTransfer

namespace LocalProfile
/-- Exact medium refinement, for all signs of the spectral coefficient. -/
lemma transfer_add (P : LocalProfile) (s t : ℝ) :
    P.transfer (s+t)=(P.transfer t).after (P.transfer s) := by
  apply RealTransfer.ext_of_action
  intro y
  rw [RealTransfer.after_act]
  exact P.flow_add y s t

/-- The fundamental functions are unique for their real coefficient. -/
lemma flow_eq_of_delta_eq (P Q : LocalProfile) (hδ : P.delta=Q.delta)
    (y : State) (x : ℝ) : P.flow y x=Q.flow y x := by
  have h := Q.global_representation
    (fun t => (P.flow y t).value) (fun t => (P.flow y t).slope)
    (P.hasDerivAt_value y)
    (by intro t; simpa [hδ] using P.hasDerivAt_slope y t) x
  simpa using h
end LocalProfile
end QuantumScattering
