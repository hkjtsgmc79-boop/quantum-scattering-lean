/- Q5: the whole two-port complex scattering matrix is continuous through E=V0.
The scalar regularization is explicitly identified with the constructed physical
amplitudes. Candidate proof source, not compiled. -/
import QuantumTunneling.PhysicalLimits

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumTunneling

def regularizedCosine (δ a:ℝ) : ℝ :=
  if δ<0 then Real.cosh (Real.sqrt (-δ)*a) else Real.cos (Real.sqrt δ*a)

@[simp] lemma regularizedCosine_zero_delta (a:ℝ) : regularizedCosine 0 a=1 := by
  simp [regularizedCosine]

lemma regularizedCosine_continuousAt_threshold (a:ℝ) :
    ContinuousAt (fun δ=>regularizedCosine δ a) 0 := by
  have hminus : ContinuousAt (fun δ:ℝ=>Real.cosh (Real.sqrt (-δ)*a)) 0 := by fun_prop
  have hplus : ContinuousAt (fun δ:ℝ=>Real.cos (Real.sqrt δ*a)) 0 := by fun_prop
  change Tendsto _ _ (𝓝 (regularizedCosine 0 a))
  rw [regularizedCosine_zero_delta]
  exact tendsto_if_same (fun δ:ℝ=>δ<0) (by simpa using hminus.tendsto)
    (by simpa using hplus.tendsto)

lemma RectangularParameters.profile_C_regularized (p:RectangularParameters) :
    p.profile.C p.width=regularizedCosine p.profile.delta p.width := by
  rcases lt_trichotomy p.energy p.height with h|h|h
  · rw [p.profile_below h]
    simp [PropagationProfile.evanescent,regularizedCosine,Real.sqrt_sq_eq_abs,
      abs_of_pos (p.kappa_pos h),show -(p.kappa^2)<0 by nlinarith [pow_pos (p.kappa_pos h) 2]]
  · simp [p.profile_critical h,PropagationProfile.critical,regularizedCosine]
  · rw [p.profile_above h]
    simp [PropagationProfile.oscillatory,regularizedCosine,not_lt.mpr (sq_nonneg p.q),
      Real.sqrt_sq_eq_abs,abs_of_pos (p.q_pos h)]

def energyWaveNumber (h m E:ℝ) : ℝ := Real.sqrt (2*m*E)/h
def energyDelta (h m V E:ℝ) : ℝ := 2*m*(E-V)/h^2
def energyAlpha (h m V E:ℝ) : ℝ :=
  (energyWaveNumber h m E^2+energyDelta h m V E)/(2*energyWaveNumber h m E)
def energyBeta (h m V E:ℝ) : ℝ :=
  (energyDelta h m V E-energyWaveNumber h m E^2)/(2*energyWaveNumber h m E)

def energyAmplitudeA (h m V a E:ℝ) : ℂ :=
  (regularizedCosine (energyDelta h m V E) a:ℂ)-
    Complex.I*(energyAlpha h m V E*regularizedKernel (energyDelta h m V E) a:ℝ)
def energyAmplitudeB (h m V a E:ℝ) : ℂ :=
  Complex.I*(energyBeta h m V E*regularizedKernel (energyDelta h m V E) a:ℝ)

def energyScatteringMatrix (h m V a E:ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j=>if i=j then energyAmplitudeB h m V a E/energyAmplitudeA h m V a E
    else 1/energyAmplitudeA h m V a E

lemma RectangularParameters.physical_amplitudes_regularized (p:RectangularParameters) :
    p.layer.A=energyAmplitudeA p.hbar p.mass p.height p.width p.energy ∧
    p.layer.B=energyAmplitudeB p.hbar p.mass p.height p.width p.energy := by
  have hC := p.profile_C_regularized
  have hS := p.profile_S_regularized
  rw [p.profile_delta] at hC hS
  have ha : p.layer.alpha = energyAlpha p.hbar p.mass p.height p.energy := by
    change (p.k^2 + p.profile.delta)/(2*p.k) = _
    rw [p.profile_delta]
    rfl
  have hb : p.layer.beta = energyBeta p.hbar p.mass p.height p.energy := by
    change (p.profile.delta - p.k^2)/(2*p.k) = _
    rw [p.profile_delta]
    rfl
  change (⟨p.profile.C p.width, -p.layer.alpha * p.profile.S p.width⟩ : ℂ) = _ ∧
    (⟨0, p.layer.beta * p.profile.S p.width⟩ : ℂ) = _
  rw [ha, hb, hC, hS]
  constructor <;> apply Complex.ext <;>
    simp only [energyAmplitudeA, energyAmplitudeB, energyDelta, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] <;> ring

lemma RectangularParameters.physical_matrix_regularized (p:RectangularParameters) :
    p.layer.scatteringMatrix=energyScatteringMatrix p.hbar p.mass p.height p.width p.energy := by
  ext i j
  simp only [ScatteringLayer.scatteringMatrix,energyScatteringMatrix,
    ScatteringLayer.reflectionAmplitude,ScatteringLayer.transmissionAmplitude,
    p.physical_amplitudes_regularized.1,p.physical_amplitudes_regularized.2]

lemma energyAmplitudeA_threshold_ne_zero (h m V a:ℝ) :
    energyAmplitudeA h m V a V≠0 := by
  intro he
  have hre := congrArg Complex.re he
  simpa [energyAmplitudeA,energyDelta,Complex.mul_re] using hre

lemma energyAmplitudes_continuous_threshold {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) :
    ContinuousAt (energyAmplitudeA h m V a) V ∧
    ContinuousAt (energyAmplitudeB h m V a) V := by
  have hk : ContinuousAt (energyWaveNumber h m) V := by unfold energyWaveNumber; fun_prop
  have hkp : 0<energyWaveNumber h m V := by unfold energyWaveNumber; positivity
  have hd : ContinuousAt (energyDelta h m V) V := by unfold energyDelta; fun_prop
  have hd0 : energyDelta h m V V=0 := by simp [energyDelta]
  have hC : ContinuousAt (fun E=>regularizedCosine (energyDelta h m V E) a) V := by
    have hc : ContinuousAt (fun δ => regularizedCosine δ a) (energyDelta h m V V) := by
      rw [hd0]
      exact regularizedCosine_continuousAt_threshold a
    simpa only [Function.comp_def] using hc.comp hd
  have hS : ContinuousAt (fun E=>regularizedKernel (energyDelta h m V E) a) V := by
    have hc : ContinuousAt (fun δ => regularizedKernel δ a) (energyDelta h m V V) := by
      rw [hd0]
      exact regularizedKernel_continuousAt_threshold a
    simpa only [Function.comp_def] using hc.comp hd
  have ha : ContinuousAt (energyAlpha h m V) V :=
    ((hk.pow 2).add hd).div (continuousAt_const.mul hk) (by positivity)
  have hb : ContinuousAt (energyBeta h m V) V :=
    (hd.sub (hk.pow 2)).div (continuousAt_const.mul hk) (by positivity)
  have hCc : ContinuousAt (fun E=>(regularizedCosine (energyDelta h m V E) a:ℂ)) V :=
    Complex.continuous_ofReal.continuousAt.comp hC
  have hAc : ContinuousAt (fun E=>((energyAlpha h m V E*
      regularizedKernel (energyDelta h m V E) a:ℝ):ℂ)) V :=
    Complex.continuous_ofReal.continuousAt.comp (ha.mul hS)
  have hBc : ContinuousAt (fun E=>((energyBeta h m V E*
      regularizedKernel (energyDelta h m V E) a:ℝ):ℂ)) V :=
    Complex.continuous_ofReal.continuousAt.comp (hb.mul hS)
  exact ⟨hCc.sub (continuousAt_const.mul hAc),continuousAt_const.mul hBc⟩

/-- Entrywise matrix continuity is the finite-dimensional matrix continuity
statement with no choice of norm needed. It includes BOTH complex phases. -/
theorem scatteringMatrix_threshold_continuity {h m V a:ℝ}
    (hh:0<h) (hm:0<m) (hV:0<V) (i j:Fin 2) :
    ContinuousAt (fun E=>energyScatteringMatrix h m V a E i j) V := by
  obtain ⟨hA,hB⟩ := energyAmplitudes_continuous_threshold (a:=a) hh hm hV
  by_cases hij:i=j
  · simpa [energyScatteringMatrix, hij, Pi.div_def] using
      hB.div hA (energyAmplitudeA_threshold_ne_zero h m V a)
  · have hOne : ContinuousAt (fun _ : ℝ => (1 : ℂ)) V := continuousAt_const
    simpa [energyScatteringMatrix, hij, Pi.div_def] using
      hOne.div hA (energyAmplitudeA_threshold_ne_zero h m V a)

end QuantumTunneling
