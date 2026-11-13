/- Q5: real two-sided critical-energy continuity, not numerical agreement. -/
import QuantumTunneling.RegularizedTransmission

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumTunneling

lemma transmissionFunction_at_threshold {h m V a:ℝ}
    (hh:0<h) (hV:0<V) :
    transmissionFunction h m V a V=(1+m*V*a^2/(2*h^2))⁻¹ := by
  unfold transmissionFunction
  simp only [sub_self,mul_zero,zero_div,regularizedKernel_zero_delta]
  congr 1
  field_simp [ne_of_gt hh,ne_of_gt hV] <;> ring

/-- The apparent pole in the separate sine/sinh formulas is removable, and the
common limit is exactly the independently constructed linear threshold state. -/
theorem transmission_continuous_at_threshold {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) :
    ContinuousAt (transmissionFunction h m V a) V := by
  have hδ : Tendsto (fun E:ℝ=>2*m*(E-V)/h^2) (𝓝 V) (𝓝 0) := by
    have hc : ContinuousAt (fun E:ℝ=>2*m*(E-V)/h^2) V := by fun_prop
    simpa using hc.tendsto
  have hS : Tendsto (fun E:ℝ=>regularizedKernel (2*m*(E-V)/h^2) a)
      (𝓝 V) (𝓝 a) := by
    simpa [Function.comp_def] using (regularizedKernel_continuousAt_threshold a).tendsto.comp hδ
  have hcoef : ContinuousAt (fun E:ℝ=>m*V^2/(2*h^2*E)) V := by
    exact continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 V) (𝓝 1) := tendsto_const_nhds
  have hden := hOne.add (hcoef.tendsto.mul (hS.pow 2))
  have hn : 1+m*V^2/(2*h^2*V)*a^2≠0 := by positivity
  have hlim := hden.inv₀ hn
  change Tendsto (fun E => (1+m*V^2/(2*h^2*E)*regularizedKernel (2*m*(E-V)/h^2) a^2)⁻¹)
    (𝓝 V) (𝓝 (transmissionFunction h m V a V))
  simpa only [transmissionFunction,sub_self,mul_zero,zero_div,
    regularizedKernel_zero_delta] using hlim

theorem transmission_threshold_limit {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) :
    Tendsto (transmissionFunction h m V a) (𝓝 V)
      (𝓝 ((1+m*V*a^2/(2*h^2))⁻¹)) := by
  simpa only [transmissionFunction_at_threshold hh hV] using
    (transmission_continuous_at_threshold (a:=a) hh hm hV).tendsto

theorem transmission_threshold_left_limit {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) :
    Tendsto (transmissionFunction h m V a) (𝓝[<] V)
      (𝓝 ((1+m*V*a^2/(2*h^2))⁻¹)) :=
  (transmission_threshold_limit (a:=a) hh hm hV).mono_left nhdsWithin_le_nhds

theorem transmission_threshold_right_limit {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) :
    Tendsto (transmissionFunction h m V a) (𝓝[>] V)
      (𝓝 ((1+m*V*a^2/(2*h^2))⁻¹)) :=
  (transmission_threshold_limit (a:=a) hh hm hV).mono_left nhdsWithin_le_nhds

/-- Parameter variation is tied back to the constructed barrier family. -/
def RectangularParameters.withEnergy (p:RectangularParameters) (E:ℝ) (hE:0<E) :
    RectangularParameters := {p with energy:=E,energy_pos:=hE}

lemma physical_energy_family_eq (p:RectangularParameters) (E:ℝ) (hE:0<E) :
    (p.withEnergy E hE).layer.T=transmissionFunction p.hbar p.mass p.height p.width E :=
  (p.withEnergy E hE).physical_transmission_regularized

end QuantumTunneling
