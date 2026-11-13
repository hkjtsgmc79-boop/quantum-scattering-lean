/-
Q5: physical limits of the observable already connected to actual currents.
Thin width, high energy (with a quantitative bound), and sub-barrier thick-width
suppression including its exact leading coefficient. Candidate, uncompiled.
-/
import QuantumTunneling.ThresholdContinuity
import QuantumTunneling.ResonanceClassification

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumTunneling

/-- For fixed energy the removable-slope propagation kernel vanishes with width. -/
lemma regularizedKernel_tendsto_zero_width (δ:ℝ) :
    Tendsto (regularizedKernel δ) (𝓝 0) (𝓝 0) := by
  by_cases hδ:δ<0
  · have ht : Tendsto (fun a:ℝ=>Real.sqrt (-δ)*a) (𝓝 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_id : Tendsto (fun a:ℝ=>a) (𝓝 0) (𝓝 0))
    have hs := continuousAt_sinhRatio_zero.tendsto.comp ht
    change Tendsto (fun a => regularizedKernel δ a) (𝓝 0) (𝓝 0)
    simpa [regularizedKernel, hδ, Function.comp_def] using
      (tendsto_id : Tendsto (fun a:ℝ=>a) (𝓝 0) (𝓝 0)).mul hs
  · have ht : Tendsto (fun a:ℝ=>Real.sqrt δ*a) (𝓝 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_id : Tendsto (fun a:ℝ=>a) (𝓝 0) (𝓝 0))
    have hs := continuousAt_sinRatio_zero.tendsto.comp ht
    change Tendsto (fun a => regularizedKernel δ a) (𝓝 0) (𝓝 0)
    simpa [regularizedKernel, hδ, Function.comp_def] using
      (tendsto_id : Tendsto (fun a:ℝ=>a) (𝓝 0) (𝓝 0)).mul hs

/-- A disappearing barrier becomes transparent, including at threshold energy.
The two-sided limit is a stronger extension statement; physical widths are positive. -/
theorem transmission_thin_limit (h m V E:ℝ) :
    Tendsto (fun a:ℝ=>transmissionFunction h m V a E) (𝓝 0) (𝓝 1) := by
  have hs := (regularizedKernel_tendsto_zero_width (2*m*(E-V)/h^2)).pow 2
  have hd : Tendsto (fun a:ℝ=>1+(m*V^2/(2*h^2*E))*
      regularizedKernel (2*m*(E-V)/h^2) a^2) (𝓝 0) (𝓝 1) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hs) using 1 <;> norm_num
  simpa [transmissionFunction] using hd.inv₀ (by norm_num : (1:ℝ)≠0)

/-- A simple rational bound, used instead of claiming the rapidly oscillating
sine itself has a limit at high energy. -/
lemma one_sub_inverse_bound {x:ℝ} (hx:0≤x) :
    0≤1-(1+x)⁻¹ ∧ 1-(1+x)⁻¹≤x := by
  have hd : 0<1+x := by linarith
  have hi : (1+x)*(1+x)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hd)
  have hn : 0≤(1+x)⁻¹ := inv_nonneg.mpr hd.le
  have hu : (1+x)⁻¹≤1 := by nlinarith [mul_nonneg hx hn]
  constructor
  · linarith
  · nlinarith [mul_le_mul_of_nonneg_left hu hx]

/-- Uniform high-energy reflection bound, independent of the oscillatory phase. -/
theorem transmission_high_energy_bound {h m V a E:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) (ha:0<a) (hE:2*V<E) :
    0≤1-transmissionFunction h m V a E ∧
      1-transmissionFunction h m V a E≤V^2/(2*E^2) := by
  have hEV:V<E := by linarith
  have hEp:0<E := lt_trans hV hEV
  have hc:0<V^2/(4*E*(E-V)) := by positivity
  have hs:Real.sin ((Real.sqrt (2*m*(E-V))/h)*a)^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq ((Real.sqrt (2*m*(E-V))/h)*a),
      sq_nonneg (Real.cos ((Real.sqrt (2*m*(E-V))/h)*a))]
  rw [transmissionFunction_above hh hm hV ha hEV]
  have hb := one_sub_inverse_bound
    (mul_nonneg hc.le (sq_nonneg (Real.sin ((Real.sqrt (2*m*(E-V))/h)*a))))
  refine ⟨hb.1,le_trans hb.2 ?_⟩
  calc
    _ ≤ V^2/(4*E*(E-V)) := by simpa using mul_le_mul_of_nonneg_left hs hc.le
    _ ≤ V^2/(2*E^2) := by
      apply div_le_div_of_nonneg_left (sq_nonneg V) (by positivity)
      nlinarith [mul_pos hEp (sub_pos.mpr hE)]

/-- Fixed finite barriers are asymptotically transparent as energy tends to infinity. -/
theorem transmission_high_energy_limit {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) (ha:0<a) :
    Tendsto (transmissionFunction h m V a) atTop (𝓝 1) := by
  have hi : Tendsto (fun E:ℝ=>E⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hu : Tendsto (fun E:ℝ=>V^2/(2*E^2)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ :ℝ=>V^2/2) atTop (𝓝 (V^2/2))).mul
      (hi.pow 2) using 1 <;> simp [div_eq_mul_inv,mul_pow] <;> ring
  have hb : ∀ᶠ E:ℝ in atTop,
      0≤1-transmissionFunction h m V a E ∧
      1-transmissionFunction h m V a E≤V^2/(2*E^2) := by
    filter_upwards [eventually_gt_atTop (2*V)] with E hE
    exact transmission_high_energy_bound hh hm hV ha hE
  have hz : Tendsto (fun E:ℝ=>1-transmissionFunction h m V a E) atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze' hu (hb.mono fun _ h=>h.1) (hb.mono fun _ h=>h.2)
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have ht := hOne.sub hz
  simpa using ht

/-- Algebraic exponential identity underlying the sharp tunneling asymptotic. -/
lemma sinh_squared_exp_negative (x:ℝ) :
    Real.sinh x^2*Real.exp (-2*x)=(1-Real.exp (-2*x))^2/4 := by
  have he : Real.exp (-2*x)=(Real.exp x)⁻¹^2 := by
    rw [show -2*x=-(x+x) by ring,Real.exp_neg,Real.exp_add]
    simp [pow_two,mul_inv_rev]
  rw [he,Real.sinh_eq,Real.exp_neg]
  field_simp [Real.exp_ne_zero x] <;> ring

lemma exp_two_mul_inverse (x:ℝ) : Real.exp (2*x)=(Real.exp (-2*x))⁻¹ := by
  rw [show -2*x=-(2*x) by ring,Real.exp_neg,inv_inv]

/-- Positive denominator after extracting the exponentially small factor. -/
lemma thick_denominator_pos {C:ℝ} (hC:0<C) (x:ℝ) :
    0<C*(1-Real.exp (-2*x))^2+4*Real.exp (-2*x) := by positivity

lemma thick_transmission_rewrite {C:ℝ} (hC:0<C) (x:ℝ) :
    (1+C*Real.sinh x^2)⁻¹=
      4*Real.exp (-2*x)/(C*(1-Real.exp (-2*x))^2+4*Real.exp (-2*x)) := by
  have hd:0<1+C*Real.sinh x^2 := by positivity
  have hi := sinh_squared_exp_negative x
  apply (eq_div_iff (ne_of_gt (thick_denominator_pos hC x))).2
  field_simp [ne_of_gt hd]
  have hscaled := congrArg (fun y:ℝ=>4*C*y) hi
  simp only [neg_mul] at hscaled
  linear_combination -hscaled

lemma thick_scaled_transmission_rewrite {C:ℝ} (hC:0<C) (x:ℝ) :
    (1+C*Real.sinh x^2)⁻¹*Real.exp (2*x)=
      4/(C*(1-Real.exp (-2*x))^2+4*Real.exp (-2*x)) := by
  rw [thick_transmission_rewrite hC,exp_two_mul_inverse]
  field_simp [Real.exp_ne_zero (-2*x),ne_of_gt (thick_denominator_pos hC x)]

lemma negative_double_wave_exponential_tendsto {κ:ℝ} (hκ:0<κ) :
    Tendsto (fun a:ℝ=>Real.exp (-2*(κ*a))) atTop (𝓝 0) := by
  have ht : Tendsto (fun a:ℝ=>(2*κ)*a) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (mul_pos (by norm_num) hκ) tendsto_id
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp ht using 1 <;> funext a <;> congr 1 <;> ring

private lemma thick_denominator_limit (C : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun a : ℝ => C * (1 - Real.exp (-2*(κ*a)))^2 + 4 * Real.exp (-2*(κ*a)))
      atTop (𝓝 C) := by
  have hz := negative_double_wave_exponential_tendsto hκ
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hFour : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have hC : Tendsto (fun _ : ℝ => C) atTop (𝓝 C) := tendsto_const_nhds
  simpa using (hC.mul ((hOne.sub hz).pow 2)).add (hFour.mul hz)

/-- Sharp asymptotic for the elementary below-barrier transmission profile. -/
theorem thick_profile_scaled_limit {C κ:ℝ} (hC:0<C) (hκ:0<κ) :
    Tendsto (fun a:ℝ=>(1+C*Real.sinh (κ*a)^2)⁻¹*Real.exp (2*(κ*a)))
      atTop (𝓝 (4/C)) := by
  have hFour : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have hlim := hFour.div (thick_denominator_limit C hκ) (ne_of_gt hC)
  convert hlim using 1
  funext a
  exact thick_scaled_transmission_rewrite hC (κ*a)

theorem thick_profile_limit {C κ:ℝ} (hC:0<C) (hκ:0<κ) :
    Tendsto (fun a:ℝ=>(1+C*Real.sinh (κ*a)^2)⁻¹) atTop (𝓝 0) := by
  have hz := negative_double_wave_exponential_tendsto hκ
  have hFour : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have hnum : Tendsto (fun a:ℝ=>4*Real.exp (-2*(κ*a))) atTop (𝓝 0) := by
    simpa using hFour.mul hz
  have hlim := hnum.div (thick_denominator_limit C hκ) (ne_of_gt hC)
  convert hlim using 1
  · funext a
    exact thick_transmission_rewrite hC (κ*a)
  · norm_num

/-- The exact prefactor is proved, not only a vague exponential upper bound. -/
theorem transmission_thick_scaled_limit {h m V E:ℝ}
    (hh:0<h) (hm:0<m) (hE:0<E) (hEV:E<V) :
    Tendsto (fun a:ℝ=>transmissionFunction h m V a E*
      Real.exp (2*((Real.sqrt (2*m*(V-E))/h)*a))) atTop
      (𝓝 (16*E*(V-E)/V^2)) := by
  have hV:0<V := lt_trans hE hEV
  have hC:0<V^2/(4*E*(V-E)) := by positivity
  have hκ:0<Real.sqrt (2*m*(V-E))/h := by positivity
  have hlim := thick_profile_scaled_limit hC hκ
  have hp : (4:ℝ)/(V^2/(4*E*(V-E)))=16*E*(V-E)/V^2 := by
    field_simp [ne_of_gt hV,ne_of_gt hE,ne_of_gt (sub_pos.mpr hEV)] <;> ring
  rw [hp] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  rw [transmissionFunction_below hh hm hV ha hE hEV]

theorem transmission_thick_limit {h m V E:ℝ}
    (hh:0<h) (hm:0<m) (hE:0<E) (hEV:E<V) :
    Tendsto (fun a:ℝ=>transmissionFunction h m V a E) atTop (𝓝 0) := by
  have hV:0<V := lt_trans hE hEV
  have hC:0<V^2/(4*E*(V-E)) := by positivity
  have hκ:0<Real.sqrt (2*m*(V-E))/h := by positivity
  apply (thick_profile_limit hC hκ).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  rw [transmissionFunction_below hh hm hV ha hE hEV]

/-- Width variation is connected to the physical barrier, not an unrelated scalar. -/
def RectangularParameters.withWidth (p:RectangularParameters) (a:ℝ) (ha:0<a) :
    RectangularParameters := {p with width:=a,width_pos:=ha}

lemma physical_width_family_eq (p:RectangularParameters) (a:ℝ) (ha:0<a) :
    (p.withWidth a ha).layer.T=transmissionFunction p.hbar p.mass p.height a p.energy :=
  (p.withWidth a ha).physical_transmission_regularized

end QuantumTunneling
