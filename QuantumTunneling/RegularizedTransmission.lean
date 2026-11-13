/-
Q5: removable singularities are handled by derivative-extended slopes.
This avoids treating sin(0)/0 or sinh(0)/0 as 1 in Lean's total division.
Candidate source, not compiled.
-/
import QuantumTunneling.CoherentCurrent
import Mathlib.Analysis.Calculus.DSlope

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumTunneling

/-- Value 1 at zero is obtained from an actual derivative, not total division. -/
def sinRatio : ℝ→ℝ := dslope Real.sin 0
def sinhRatio : ℝ→ℝ := dslope Real.sinh 0

@[simp] lemma sinRatio_zero : sinRatio 0=1 := by
  simp [sinRatio,dslope_same,Real.deriv_sin]
@[simp] lemma sinhRatio_zero : sinhRatio 0=1 := by
  simp [sinhRatio,dslope_same,Real.deriv_sinh]
lemma sinRatio_of_ne {x:ℝ} (hx:x≠0) : sinRatio x=Real.sin x/x := by
  rw [sinRatio,dslope_of_ne Real.sin hx]
  simp [slope,smul_eq_mul,div_eq_mul_inv,mul_comm]
lemma sinhRatio_of_ne {x:ℝ} (hx:x≠0) : sinhRatio x=Real.sinh x/x := by
  rw [sinhRatio,dslope_of_ne Real.sinh hx]
  simp [slope,smul_eq_mul,div_eq_mul_inv,mul_comm]
lemma continuousAt_sinRatio_zero : ContinuousAt sinRatio 0 := by
  exact continuousAt_dslope_same.mpr (Real.hasDerivAt_sin 0).differentiableAt
lemma continuousAt_sinhRatio_zero : ContinuousAt sinhRatio 0 := by
  exact continuousAt_dslope_same.mpr (Real.hasDerivAt_sinh 0).differentiableAt

/-- S_delta(a), extended across the zero interior wave number. -/
def regularizedKernel (δ a : ℝ) : ℝ :=
  if δ<0 then a*sinhRatio (Real.sqrt (-δ)*a)
  else a*sinRatio (Real.sqrt δ*a)

@[simp] lemma regularizedKernel_zero_delta (a:ℝ) : regularizedKernel 0 a=a := by
  simp [regularizedKernel]
@[simp] lemma regularizedKernel_zero_width (δ:ℝ) : regularizedKernel δ 0=0 := by
  simp [regularizedKernel]

lemma regularizedKernel_evanescent {κ a:ℝ} (hκ:0<κ) (ha:0<a) :
    regularizedKernel (-(κ^2)) a=Real.sinh (κ*a)/κ := by
  have hn : -(κ^2)<0 := by nlinarith [pow_pos hκ 2]
  rw [regularizedKernel,if_pos hn,neg_neg,Real.sqrt_sq_eq_abs,abs_of_pos hκ,
    sinhRatio_of_ne (ne_of_gt (mul_pos hκ ha))]
  field_simp [ne_of_gt hκ,ne_of_gt ha] <;> ring

lemma regularizedKernel_oscillatory {q a:ℝ} (hq:0<q) (ha:0<a) :
    regularizedKernel (q^2) a=Real.sin (q*a)/q := by
  rw [regularizedKernel,if_neg (not_lt.mpr (sq_nonneg q)),Real.sqrt_sq_eq_abs,abs_of_pos hq,
    sinRatio_of_ne (ne_of_gt (mul_pos hq ha))]
  field_simp [ne_of_gt hq,ne_of_gt ha] <;> ring

/-- A parameter-dependent switch preserves a common limit even when its
condition changes infinitely often. No continuity of the Boolean condition. -/
lemma tendsto_if_same {α β:Type*} [TopologicalSpace β] {l:Filter α} {b:β}
    {f g:α→β} (P:α→Prop) [DecidablePred P]
    (hf:Tendsto f l (𝓝 b)) (hg:Tendsto g l (𝓝 b)) :
    Tendsto (fun x=>if P x then f x else g x) l (𝓝 b) := by
  rw [Filter.tendsto_def]
  intro U hU
  filter_upwards [hf.eventually hU,hg.eventually hU] with x hx hy
  change U (if P x then f x else g x)
  by_cases h : P x
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

/-- Both open energy branches converge to the same threshold propagation. -/
theorem regularizedKernel_continuousAt_threshold (a:ℝ) :
    ContinuousAt (fun δ=>regularizedKernel δ a) 0 := by
  have hn : Tendsto (fun δ:ℝ=>Real.sqrt (-δ)*a) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun δ:ℝ=>Real.sqrt (-δ)*a) 0 := by fun_prop
    simpa using h.tendsto
  have hp : Tendsto (fun δ:ℝ=>Real.sqrt δ*a) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun δ:ℝ=>Real.sqrt δ*a) 0 := by fun_prop
    simpa using h.tendsto
  have hs : Tendsto (fun δ:ℝ=>a*sinhRatio (Real.sqrt (-δ)*a)) (𝓝 0) (𝓝 a) := by
    simpa using tendsto_const_nhds.mul (continuousAt_sinhRatio_zero.tendsto.comp hn)
  have ht : Tendsto (fun δ:ℝ=>a*sinRatio (Real.sqrt δ*a)) (𝓝 0) (𝓝 a) := by
    simpa using tendsto_const_nhds.mul (continuousAt_sinRatio_zero.tendsto.comp hp)
  change Tendsto _ _ (𝓝 (regularizedKernel 0 a))
  rw [regularizedKernel_zero_delta]
  exact tendsto_if_same (fun δ:ℝ=>δ<0) hs ht

/-- A scalar observable allowing energy/width limits; it equals the physical
current-ratio transmission for EVERY admissible physical parameter tuple. -/
def transmissionFunction (hbar mass height width energy:ℝ) : ℝ :=
  (1+mass*height^2/(2*hbar^2*energy)*
    regularizedKernel (2*mass*(energy-height)/hbar^2) width ^2)⁻¹

namespace RectangularParameters
lemma profile_S_regularized (p:RectangularParameters) :
    p.profile.S p.width=regularizedKernel p.profile.delta p.width := by
  rcases lt_trichotomy p.energy p.height with h|h|h
  · rw [p.profile_below h]
    exact (regularizedKernel_evanescent (p.kappa_pos h) p.width_pos).symm
  · simp [p.profile_critical h,PropagationProfile.critical]
  · rw [p.profile_above h]
    exact (regularizedKernel_oscillatory (p.q_pos h) p.width_pos).symm

/-- This bridge prevents an unrelated algebraic function being used in place of
physical transmission when proving parameter limits. -/
theorem physical_transmission_regularized (p:RectangularParameters) :
    p.layer.T=transmissionFunction p.hbar p.mass p.height p.width p.energy := by
  rw [p.layer.T_formula,p.beta_sq_physical]
  change (1+p.mass*p.height^2/(2*p.hbar^2*p.energy)*(p.profile.S p.width)^2)⁻¹=_
  rw [p.profile_S_regularized,p.profile_delta]
  rfl
end RectangularParameters

lemma transmissionFunction_above {h m V a E:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) (ha:0<a) (hE:V<E) :
    transmissionFunction h m V a E=
      (1+V^2/(4*E*(E-V))*Real.sin ((Real.sqrt (2*m*(E-V))/h)*a)^2)⁻¹ := by
  let p:RectangularParameters:=⟨h,m,E,V,a,hh,hm,lt_trans hV hE,hV,ha⟩
  rw [←p.physical_transmission_regularized]
  exact p.transmission_above hE

lemma transmissionFunction_below {h m V a E:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) (ha:0<a) (hE:0<E) (hEV:E<V) :
    transmissionFunction h m V a E=
      (1+V^2/(4*E*(V-E))*Real.sinh ((Real.sqrt (2*m*(V-E))/h)*a)^2)⁻¹ := by
  let p:RectangularParameters:=⟨h,m,E,V,a,hh,hm,hE,hV,ha⟩
  rw [←p.physical_transmission_regularized]
  exact p.transmission_below hEV

lemma transmissionFunction_bounds {h m V a E:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) (ha:0<a) (hE:0<E) :
    0<transmissionFunction h m V a E ∧ transmissionFunction h m V a E≤1 := by
  let p:RectangularParameters:=⟨h,m,E,V,a,hh,hm,hE,hV,ha⟩
  rw [←p.physical_transmission_regularized]
  exact ⟨p.layer.T_pos,p.layer.T_le_one⟩

end QuantumTunneling
