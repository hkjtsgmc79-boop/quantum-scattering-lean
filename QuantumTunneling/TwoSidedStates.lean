/-
Q5: actual right-incident waves and arbitrary coherent two-sided incidence.
All equations use actual derivatives. Interface phase conventions match S.
Candidate proof source, not a verification report.
-/
import QuantumTunneling.ScatteringMatrix

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumTunneling

lemma plane_neg_argument (k x : ℝ) : plane k (-x)=plane (-k) x := by
  unfold plane; congr 1; ring

/-- A classical physical state. No elementary basis representation, amplitudes,
probability conservation or uniqueness is assumed by this definition. -/
structure StationaryState (p : RectangularParameters) (f : ℝ→ℂ) : Prop where
  regularity : ContDiff ℝ 1 f
  equation : ∀ x, x≠0 → x≠p.width →
    HasDerivAt (deriv f) (p.layer.odeCoefficient x • f x) x

namespace StationaryState
lemma differentiable {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) : Differentiable ℝ f :=
  (contDiff_one_iff_deriv.mp h.regularity).1
lemma continuous {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) : Continuous f := h.differentiable.continuous
lemma continuous_derivative {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) : Continuous (deriv f) :=
  (contDiff_one_iff_deriv.mp h.regularity).2
lemma hasDerivAt {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (h.differentiable x).hasDerivAt

/-- The ODE coefficient is not a replacement physical law: this recovers the
literal Schrödinger equation from the explicitly proved coefficient relation. -/
theorem schrodinger {p : RectangularParameters} {f : ℝ→ℂ}
    (h : StationaryState p f) (x : ℝ) (h0 : x≠0) (ha : x≠p.width) :
    (-p.kinetic) • deriv (deriv f) x+p.potential x • f x=p.energy • f x := by
  rw [(h.equation x h0 ha).deriv,smul_smul,← add_smul,p.odeCoefficient_energy x h0 ha]

lemma linear_combination {p : RectangularParameters} {f g : ℝ→ℂ}
    (hf : StationaryState p f) (hg : StationaryState p g) (c d : ℂ) :
    StationaryState p (fun x => c*f x+d*g x) := by
  have hd : deriv (fun x=>c*f x+d*g x)=fun x=>c*deriv f x+d*deriv g x := by
    funext x
    exact (((hf.hasDerivAt x).const_mul c).add ((hg.hasDerivAt x).const_mul d)).deriv
  constructor
  · exact (contDiff_const.mul hf.regularity).add (contDiff_const.mul hg.regularity)
  · intro x h0 ha
    rw [hd]
    convert ((hf.equation x h0 ha).const_mul c).add
      ((hg.equation x h0 ha).const_mul d) using 1 <;>
      simp only [Complex.real_smul] <;> ring
end StationaryState

namespace RectangularParameters
lemma wave_stationary (p : RectangularParameters) : StationaryState p p.wave := by
  constructor
  · exact p.layer.contDiff_one_normalizedWave
  · intro x h0 ha
    change HasDerivAt (deriv p.layer.normalizedWave) _ x
    rw [p.layer.deriv_normalized]
    exact p.layer.hasDerivAt_normalizedD x h0 ha

lemma odeCoefficient_reflection (p : RectangularParameters) (x : ℝ)
    (h0 : x≠0) (ha : x≠p.width) :
    p.layer.odeCoefficient (p.width-x)=p.layer.odeCoefficient x := by
  unfold ScatteringLayer.odeCoefficient layer
  by_cases hx : x<0
  · have ha1 : ¬p.width-x<0 := by linarith [p.width_pos]
    have ha2 : ¬p.width-x<p.width := by linarith
    simp [hx,ha1,ha2]
  · by_cases hxa : x<p.width
    · have h1 : ¬p.width-x<0 := by linarith
      have h2 : p.width-x<p.width := by have := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm h0); linarith
      simp [hx,hxa,h1,h2]
    · have h1 : p.width-x<0 := by have := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm ha); linarith
      simp [hx,hxa,h1]

/-- Mirror the left solution about the centre of the actual barrier. -/
def rightWave (p : RectangularParameters) (x : ℝ) : ℂ := p.wave (p.width-x)
def rightWaveD (p : RectangularParameters) (x : ℝ) : ℂ := -p.waveD (p.width-x)

lemma hasDerivAt_rightWave (p : RectangularParameters) (x : ℝ) :
    HasDerivAt p.rightWave (p.rightWaveD x) x := by
  have h := (p.layer.hasDerivAt_normalized (p.width-x)).scomp x
    ((hasDerivAt_id x).const_sub p.width)
  change HasDerivAt (fun t => p.layer.normalizedWave (p.width - t)) _ x
  simpa [Function.comp_def, rightWaveD, waveD] using h

lemma deriv_rightWave (p : RectangularParameters) : deriv p.rightWave=p.rightWaveD :=
  funext fun x => (p.hasDerivAt_rightWave x).deriv

lemma rightWave_stationary (p : RectangularParameters) : StationaryState p p.rightWave := by
  constructor
  · exact p.wave_stationary.regularity.comp (contDiff_const.sub contDiff_id)
  · intro x h0 ha
    rw [p.deriv_rightWave]
    have hy0 : p.width-x≠0 := by intro h; apply ha; linarith
    have hya : p.width-x≠p.width := by intro h; apply h0; linarith
    have hd := ((p.layer.hasDerivAt_normalizedD (p.width-x) hy0 hya).scomp x
      ((hasDerivAt_id x).const_sub p.width)).neg
    convert hd using 1
    · rfl
    · simp only [rightWave, wave, p.odeCoefficient_reflection x h0 ha,
        neg_smul, smul_neg, neg_neg, one_smul]

lemma rightWave_left (p : RectangularParameters) (x : ℝ) (hx : x<0) :
    p.rightWave x=p.transmissionAmplitude*plane (-p.k) x := by
  have hy : p.width<p.width-x := by linarith
  rw [rightWave,(complete_rectangular_scattering p).right_scattering _ hy]
  congr 1
  rw [show p.width-x-p.width = -x by ring,plane_neg_argument]

lemma rightWave_right (p : RectangularParameters) (x : ℝ) (hx : p.width<x) :
    p.rightWave x=plane (-p.k) (x-p.width)+p.reflectionAmplitude*plane p.k (x-p.width) := by
  have hy : p.width-x<0 := by linarith
  rw [rightWave,(complete_rectangular_scattering p).left_scattering _ hy]
  rw [show p.width-x=-(x-p.width) by ring,plane_neg_argument,plane_neg_argument,neg_neg]

lemma current_rightWave (p : RectangularParameters) (x : ℝ) :
    current p.hbar p.mass p.rightWave x =
      -((p.hbar/p.mass)*p.k*p.layer.T) := by
  rw [current,p.deriv_rightWave]
  have hleft := p.layer.current_normalized p.hbar p.mass (p.width-x)
  change (p.hbar/p.mass)*fluxForm (p.wave (p.width-x)) (-p.waveD (p.width-x)) = _
  rw [current,p.layer.deriv_normalized] at hleft
  change (p.hbar/p.mass)*fluxForm (p.wave (p.width-x)) (p.waveD (p.width-x)) = _ at hleft
  rw [show fluxForm (p.wave (p.width-x)) (-p.waveD (p.width-x))=
    -fluxForm (p.wave (p.width-x)) (p.waveD (p.width-x)) by simp [fluxForm]; ring]
  change (p.hbar/p.mass)*fluxForm (p.wave (p.width-x)) (p.waveD (p.width-x)) =
    (p.hbar/p.mass)*p.k*p.layer.T at hleft
  linarith

/-- Arbitrary coherent incidence from both sides, including either pure channel. -/
def coherentWave (p : RectangularParameters) (inL inR : ℂ) (x : ℝ) : ℂ :=
  inL*p.wave x+inR*p.rightWave x

lemma coherentWave_stationary (p : RectangularParameters) (inL inR : ℂ) :
    StationaryState p (p.coherentWave inL inR) :=
  p.wave_stationary.linear_combination p.rightWave_stationary inL inR

lemma coherentWave_left (p : RectangularParameters) (inL inR : ℂ)
    (x : ℝ) (hx : x<0) : p.coherentWave inL inR x =
    freeWave p.k inL (p.layer.outgoingLeft inL inR) x := by
  unfold coherentWave
  rw [(complete_rectangular_scattering p).left_scattering x hx,p.rightWave_left x hx]
  simp only [freeWave,ScatteringLayer.outgoingLeft,reflectionAmplitude,transmissionAmplitude]
  ring

lemma coherentWave_right (p : RectangularParameters) (inL inR : ℂ)
    (x : ℝ) (hx : p.width<x) : p.coherentWave inL inR x =
    freeWave p.k (p.layer.outgoingRight inL inR) inR (x-p.width) := by
  unfold coherentWave
  rw [(complete_rectangular_scattering p).right_scattering x hx,p.rightWave_right x hx]
  simp only [freeWave,ScatteringLayer.outgoingRight,reflectionAmplitude,transmissionAmplitude]
  ring
end RectangularParameters

/-- Radiation conditions only concern the two exterior intervals. The interior
wave is not presumed to belong to a chosen elementary span. -/
structure TwoSidedRadiation (p : RectangularParameters) (f : ℝ→ℂ)
    (inL inR outL outR : ℂ) : Prop where
  left : ∀ x, x<0 → f x=freeWave p.k inL outL x
  right : ∀ x, p.width<x → f x=freeWave p.k outR inR (x-p.width)

lemma coherentWave_radiation (p : RectangularParameters) (inL inR : ℂ) :
    TwoSidedRadiation p (p.coherentWave inL inR) inL inR
      (p.layer.outgoingLeft inL inR) (p.layer.outgoingRight inL inR) :=
  ⟨p.coherentWave_left inL inR,p.coherentWave_right inL inR⟩

end QuantumTunneling
