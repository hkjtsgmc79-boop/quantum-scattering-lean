/-
Q5: deriving exterior plane-wave representations from the actual free ODE.
Incoming channels may be specified only by limits at ±infinity. Outgoing
coefficients and exact exterior representations are then conclusions.
Candidate source, not kernel checked.
-/
import QuantumTunneling.CoherentCurrent

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumTunneling

lemma plane_mul_opposite (k x:ℝ) : plane k x*plane (-k) x=1 := by
  apply Complex.ext
  · simp [plane,cis,Complex.mul_re,neg_mul,Real.cos_neg,Real.sin_neg,
      ←pow_two,Real.cos_sq_add_sin_sq]
  · simp [plane,cis,Complex.mul_im,neg_mul,Real.cos_neg,Real.sin_neg] <;> ring

def rightChannelAt (k:ℝ) (z v:ℂ) (y:ℝ) : ℂ :=
  (z+v/((k:ℂ)*Complex.I))/2*plane (-k) y

def leftChannelAt (k:ℝ) (z v:ℂ) (y:ℝ) : ℂ :=
  (z-v/((k:ℂ)*Complex.I))/2*plane k y

def rightChannel (p:RectangularParameters) (origin:ℝ) (f:ℝ→ℂ) (x:ℝ) : ℂ :=
  rightChannelAt p.k (f x) (deriv f x) (x-origin)
def leftChannel (p:RectangularParameters) (origin:ℝ) (f:ℝ→ℂ) (x:ℝ) : ℂ :=
  leftChannelAt p.k (f x) (deriv f x) (x-origin)

lemma channel_reconstruct (k:ℝ) (z v:ℂ) (y:ℝ) :
    z=rightChannelAt k z v y*plane k y+leftChannelAt k z v y*plane (-k) y := by
  calc
    z=(z+v/((k:ℂ)*Complex.I))/2+(z-v/((k:ℂ)*Complex.I))/2 := by ring
    _=(z+v/((k:ℂ)*Complex.I))/2*(plane (-k) y*plane k y)+
        (z-v/((k:ℂ)*Complex.I))/2*(plane k y*plane (-k) y) := by
      rw [plane_mul_opposite,show plane (-k) y*plane k y=1 by
        rw [mul_comm,plane_mul_opposite]]; ring
    _=_ := by unfold rightChannelAt leftChannelAt; ring

lemma rightChannelAt_free {k:ℝ} (hk:k≠0) (A B:ℂ) (x:ℝ) :
    rightChannelAt k (freeWave k A B x) (freeWaveD k A B x) x=A := by
  have hkc:(k:ℂ)≠0 := by exact_mod_cast hk
  calc
    _=A*(plane k x*plane (-k) x) := by
      unfold rightChannelAt freeWave freeWaveD planeD
      push_cast
      field_simp [hkc,Complex.I_ne_zero] <;> ring
    _=A := by rw [plane_mul_opposite,mul_one]

lemma leftChannelAt_free {k:ℝ} (hk:k≠0) (A B:ℂ) (x:ℝ) :
    leftChannelAt k (freeWave k A B x) (freeWaveD k A B x) x=B := by
  have hkc:(k:ℂ)≠0 := by exact_mod_cast hk
  calc
    _=B*(plane (-k) x*plane k x) := by
      unfold leftChannelAt freeWave freeWaveD planeD
      push_cast
      field_simp [hkc,Complex.I_ne_zero] <;> ring
    _=B := by rw [mul_comm (plane (-k) x),plane_mul_opposite,mul_one]

/-- Free Helmholtz evolution leaves both travelling-channel coefficients fixed. -/
lemma channel_derivatives_zero (p:RectangularParameters) (o x:ℝ) (f:ℝ→ℂ)
    (hf:HasDerivAt f (deriv f x) x)
    (hff:HasDerivAt (deriv f) (-(p.k^2) • f x) x) :
    HasDerivAt (rightChannel p o f) 0 x ∧ HasDerivAt (leftChannel p o f) 0 x := by
  have hp : HasDerivAt (fun y=>plane p.k (y-o)) (planeD p.k (x-o)) x := by
    simpa [Function.comp_def] using (hasDerivAt_plane p.k (x-o)).scomp x ((hasDerivAt_id x).sub_const o)
  have hn : HasDerivAt (fun y=>plane (-p.k) (y-o)) (planeD (-p.k) (x-o)) x := by
    simpa [Function.comp_def] using (hasDerivAt_plane (-p.k) (x-o)).scomp x ((hasDerivAt_id x).sub_const o)
  have hkc:(p.k:ℂ)≠0 := by exact_mod_cast ne_of_gt p.k_pos
  constructor
  · have hd := (((hf.add (hff.div_const ((p.k:ℂ)*Complex.I))).div_const 2).mul hn)
    convert hd using 1
    · rfl
    · simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow, Complex.ofReal_neg, Pi.add_apply, Pi.sub_apply, planeD]
      field_simp [hkc, Complex.I_ne_zero]
      ring_nf
      simp [Complex.I_sq] <;> ring
  · have hd := (((hf.sub (hff.div_const ((p.k:ℂ)*Complex.I))).div_const 2).mul hp)
    convert hd using 1
    · rfl
    · simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow, Complex.ofReal_neg, Pi.add_apply, Pi.sub_apply, planeD]
      field_simp [hkc, Complex.I_ne_zero]
      ring_nf
      simp [Complex.I_sq] <;> ring

namespace StationaryState
lemma free_left_channels {p:RectangularParameters} {f:ℝ→ℂ}
    (h:StationaryState p f) (x:ℝ) (hx:x<0) :
    rightChannel p 0 f x=rightChannel p 0 f (-1) ∧
    leftChannel p 0 f x=leftChannel p 0 f (-1) := by
  have hd : ∀ z∈Iio (0:ℝ), HasDerivAt (rightChannel p 0 f) 0 z ∧
      HasDerivAt (leftChannel p 0 f) 0 z := by
    intro z hz
    change z < 0 at hz
    apply channel_derivatives_zero p 0 z f (h.hasDerivAt z)
    simpa [ScatteringLayer.odeCoefficient, RectangularParameters.layer,hz] using
      h.equation z (ne_of_lt hz) (ne_of_lt (lt_trans hz p.width_pos))
  constructor
  · exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0:ℝ)).isPreconnected
      (fun z hz=>(hd z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz=>(hd z hz).1.deriv) hx (by norm_num)
  · exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0:ℝ)).isPreconnected
      (fun z hz=>(hd z hz).2.differentiableAt.differentiableWithinAt)
      (fun z hz=>(hd z hz).2.deriv) hx (by norm_num)

lemma free_right_channels {p:RectangularParameters} {f:ℝ→ℂ}
    (h:StationaryState p f) (x:ℝ) (hx:p.width<x) :
    rightChannel p p.width f x=rightChannel p p.width f (p.width+1) ∧
    leftChannel p p.width f x=leftChannel p p.width f (p.width+1) := by
  have hd : ∀ z∈Ioi p.width, HasDerivAt (rightChannel p p.width f) 0 z ∧
      HasDerivAt (leftChannel p p.width f) 0 z := by
    intro z hz
    change p.width < z at hz
    apply channel_derivatives_zero p p.width z f (h.hasDerivAt z)
    simpa [ScatteringLayer.odeCoefficient, RectangularParameters.layer,not_lt.mpr (le_of_lt (lt_trans p.width_pos hz)),
      not_lt.mpr (le_of_lt hz)] using
      h.equation z (ne_of_gt (lt_trans p.width_pos hz)) (ne_of_gt hz)
  constructor
  · exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi p.width).isPreconnected
      (fun z hz=>(hd z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz=>(hd z hz).1.deriv) hx (show p.width < p.width+1 by linarith)
  · exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi p.width).isPreconnected
      (fun z hz=>(hd z hz).2.differentiableAt.differentiableWithinAt)
      (fun z hz=>(hd z hz).2.deriv) hx (show p.width < p.width+1 by linarith)

/-- Exterior basis completeness follows from the free ODE, not a wave ansatz. -/
theorem derived_exterior_modes {p:RectangularParameters} {f:ℝ→ℂ}
    (h:StationaryState p f) :
    TwoSidedRadiation p f (rightChannel p 0 f (-1))
      (leftChannel p p.width f (p.width+1))
      (leftChannel p 0 f (-1)) (rightChannel p p.width f (p.width+1)) := by
  constructor
  · intro x hx
    have hr := channel_reconstruct p.k (f x) (deriv f x) (x-0)
    change f x=rightChannel p 0 f x*plane p.k (x-0)+
      leftChannel p 0 f x*plane (-p.k) (x-0) at hr
    rw [(h.free_left_channels x hx).1,(h.free_left_channels x hx).2] at hr
    simpa only [sub_zero,freeWave] using hr
  · intro x hx
    have hr := channel_reconstruct p.k (f x) (deriv f x) (x-p.width)
    change f x=rightChannel p p.width f x*plane p.k (x-p.width)+
      leftChannel p p.width f x*plane (-p.k) (x-p.width) at hr
    rw [(h.free_right_channels x hx).1,(h.free_right_channels x hx).2] at hr
    exact hr
end StationaryState

/-- Only incoming asymptotic data are prescribed. No outgoing coefficients or
interior/exterior elementary representation is supplied as an assumption. -/
def IncomingAtInfinity (p:RectangularParameters) (iL iR:ℂ) (f:ℝ→ℂ) : Prop :=
  StationaryState p f ∧
  Tendsto (rightChannel p 0 f) atBot (𝓝 iL) ∧
  Tendsto (leftChannel p p.width f) atTop (𝓝 iR)

/-- The asymptotic formulation and the exact radiation formulation coincide. -/
theorem incoming_at_infinity_iff_admissible (p:RectangularParameters) (iL iR:ℂ) (f:ℝ→ℂ) :
    IncomingAtInfinity p iL iR f ↔ AdmissibleScattering p iL iR f := by
  constructor
  · rintro ⟨hs,hL,hR⟩
    have hLc : Tendsto (rightChannel p 0 f) atBot (𝓝 (rightChannel p 0 f (-1))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
      exact (hs.free_left_channels x hx).1.symm
    have hRc : Tendsto (leftChannel p p.width f) atTop
        (𝓝 (leftChannel p p.width f (p.width+1))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop p.width] with x hx
      exact (hs.free_right_channels x hx).2.symm
    have heL := tendsto_nhds_unique hLc hL
    have heR := tendsto_nhds_unique hRc hR
    refine ⟨hs,leftChannel p 0 f (-1),rightChannel p p.width f (p.width+1),?_⟩
    simpa only [heL,heR] using hs.derived_exterior_modes
  · rintro ⟨hs,oL,oR,hr⟩
    refine ⟨hs,?_,?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
      symm
      unfold rightChannel
      rw [hr.left x hx,(hr.hasDerivAt_left x hx).deriv,sub_zero]
      exact rightChannelAt_free (ne_of_gt p.k_pos) iL oL x
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop p.width] with x hx
      symm
      unfold leftChannel
      rw [hr.right x hx,(hr.hasDerivAt_right x hx).deriv]
      exact leftChannelAt_free (ne_of_gt p.k_pos) oR iR (x-p.width)

/-- Full classical uniqueness with incoming channels specified at infinity. -/
theorem existsUnique_incoming_at_infinity (p:RectangularParameters) (iL iR:ℂ) :
    ∃! f:ℝ→ℂ, IncomingAtInfinity p iL iR f := by
  obtain ⟨f,hf,hu⟩ := existsUnique_two_sided_state p iL iR
  refine ⟨f,(incoming_at_infinity_iff_admissible p iL iR f).mpr hf,?_⟩
  intro g hg
  exact hu g ((incoming_at_infinity_iff_admissible p iL iR g).mp hg)

end QuantumTunneling
