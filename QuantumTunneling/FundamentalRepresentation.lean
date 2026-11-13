/-
Q5: an arbitrary classical solution is represented by the elementary basis.
The representation is PROVED from the ODE, not imposed as an ansatz.
Source candidate; actual Lean compilation is still required.
-/
import QuantumTunneling.IntervalRigidity

noncomputable section
open Set
namespace QuantumTunneling
namespace PropagationProfile

lemma continuous_C (P : PropagationProfile) : Continuous P.C :=
  (show Differentiable ℝ P.C from fun x => (P.C_deriv x).differentiableAt).continuous
lemma continuous_S (P : PropagationProfile) : Continuous P.S :=
  (show Differentiable ℝ P.S from fun x => (P.S_deriv x).differentiableAt).continuous

/-- Two inverse-fundamental-matrix coefficients of a possibly unknown solution. -/
def firstCoefficient (P : PropagationProfile) (o : ℝ) (f v : ℝ → ℂ) (x : ℝ) : ℂ :=
  (P.C (x-o) : ℂ)*f x - (P.S (x-o) : ℂ)*v x

def secondCoefficient (P : PropagationProfile) (o : ℝ) (f v : ℝ → ℂ) (x : ℝ) : ℂ :=
  (P.delta : ℂ)*(P.S (x-o) : ℂ)*f x + (P.C (x-o) : ℂ)*v x

lemma hasDerivAt_shift_C (P : PropagationProfile) (o x : ℝ) :
    HasDerivAt (fun y => (P.C (y-o) : ℂ))
      ((-P.delta*P.S (x-o) : ℝ) : ℂ) x := by
  simpa [Function.comp_def] using ((P.C_deriv (x-o)).scomp x ((hasDerivAt_id x).sub_const o)).ofReal_comp

lemma hasDerivAt_shift_S (P : PropagationProfile) (o x : ℝ) :
    HasDerivAt (fun y => (P.S (y-o) : ℂ)) (P.C (x-o) : ℂ) x := by
  simpa [Function.comp_def] using ((P.S_deriv (x-o)).scomp x ((hasDerivAt_id x).sub_const o)).ofReal_comp

lemma hasDerivAt_firstCoefficient_zero (P : PropagationProfile) (o x : ℝ)
    (f v : ℝ → ℂ) (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-P.delta • f x) x) :
    HasDerivAt (P.firstCoefficient o f v) 0 x := by
  have h := ((P.hasDerivAt_shift_C o x).mul hf).sub
    ((P.hasDerivAt_shift_S o x).mul hv)
  convert h using 1
  · rfl
  · simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

lemma hasDerivAt_secondCoefficient_zero (P : PropagationProfile) (o x : ℝ)
    (f v : ℝ → ℂ) (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-P.delta • f x) x) :
    HasDerivAt (P.secondCoefficient o f v) 0 x := by
  have h := (((P.hasDerivAt_shift_S o x).const_mul (P.delta : ℂ)).mul hf).add
    ((P.hasDerivAt_shift_C o x).mul hv)
  convert h using 1
  · rfl
  · simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

lemma reconstruct_value (P : PropagationProfile) (o x : ℝ) (f v : ℝ → ℂ) :
    f x = P.firstCoefficient o f v x*(P.C (x-o) : ℂ) +
      P.secondCoefficient o f v x*(P.S (x-o) : ℂ) := by
  have hi : (P.C (x-o) : ℂ)^2 + (P.delta : ℂ)*(P.S (x-o) : ℂ)^2 = 1 := by
    exact_mod_cast P.invariant (x-o)
  calc
    f x = f x*((P.C (x-o) : ℂ)^2+(P.delta : ℂ)*(P.S (x-o) : ℂ)^2) := by rw [hi,mul_one]
    _ = _ := by unfold firstCoefficient secondCoefficient; ring

lemma reconstruct_derivative (P : PropagationProfile) (o x : ℝ) (f v : ℝ → ℂ) :
    v x = -(P.delta : ℂ)*P.firstCoefficient o f v x*(P.S (x-o) : ℂ) +
      P.secondCoefficient o f v x*(P.C (x-o) : ℂ) := by
  have hi : (P.C (x-o) : ℂ)^2 + (P.delta : ℂ)*(P.S (x-o) : ℂ)^2 = 1 := by
    exact_mod_cast P.invariant (x-o)
  calc
    v x = v x*((P.C (x-o) : ℂ)^2+(P.delta : ℂ)*(P.S (x-o) : ℂ)^2) := by rw [hi,mul_one]
    _ = _ := by unfold firstCoefficient secondCoefficient; ring

/-- Completeness of the fundamental pair for arbitrary C1 solutions on an
interval, with the ODE required only in the OPEN interval. Endpoints can be
potential discontinuities. In particular the critical linear case is covered. -/
theorem representation_on_closed_interval (P : PropagationProfile)
    {l r o : ℝ} (hlr : l<r) (ho : o∈Icc l r) (f v : ℝ → ℂ)
    (hf : Continuous f) (hv : Continuous v)
    (hfv : ∀ x∈Ioo l r, HasDerivAt f (v x) x)
    (hode : ∀ x∈Ioo l r, HasDerivAt v (-P.delta • f x) x)
    (x : ℝ) (hx : x∈Icc l r) :
    f x = f o*(P.C (x-o) : ℂ)+v o*(P.S (x-o) : ℂ) ∧
    v x = -(P.delta : ℂ)*f o*(P.S (x-o) : ℂ)+v o*(P.C (x-o) : ℂ) := by
  have hC : Continuous (fun y => (P.C (y-o) : ℂ)) :=
    Complex.continuous_ofReal.comp (P.continuous_C.comp (continuous_id.sub continuous_const))
  have hS : Continuous (fun y => (P.S (y-o) : ℂ)) :=
    Complex.continuous_ofReal.comp (P.continuous_S.comp (continuous_id.sub continuous_const))
  have hF : Continuous (P.firstCoefficient o f v) := (hC.mul hf).sub (hS.mul hv)
  have hH : Continuous (P.secondCoefficient o f v) :=
    ((continuous_const.mul hS).mul hf).add (hC.mul hv)
  have hc := constant_on_Icc_of_deriv_zero hlr hF
    (fun y hy => P.hasDerivAt_firstCoefficient_zero o y f v (hfv y hy) (hode y hy)) hx ho
  have hd := constant_on_Icc_of_deriv_zero hlr hH
    (fun y hy => P.hasDerivAt_secondCoefficient_zero o y f v (hfv y hy) (hode y hy)) hx ho
  have hc0 : P.firstCoefficient o f v o=f o := by simp [firstCoefficient,P.C_zero,P.S_zero]
  have hd0 : P.secondCoefficient o f v o=v o := by simp [secondCoefficient,P.C_zero,P.S_zero]
  rw [hc0] at hc
  rw [hd0] at hd
  exact ⟨by simpa only [hc,hd] using P.reconstruct_value o x f v,
    by simpa only [hc,hd] using P.reconstruct_derivative o x f v⟩

/-- Genuine Cauchy uniqueness, not merely uniqueness of four guessed coefficients. -/
theorem cauchy_unique_on_closed_interval (P : PropagationProfile)
    {l r o : ℝ} (hlr : l<r) (ho : o∈Icc l r)
    (f v g w : ℝ→ℂ) (hf : Continuous f) (hv : Continuous v)
    (hg : Continuous g) (hw : Continuous w)
    (hf' : ∀ x∈Ioo l r, HasDerivAt f (v x) x)
    (hv' : ∀ x∈Ioo l r, HasDerivAt v (-P.delta • f x) x)
    (hg' : ∀ x∈Ioo l r, HasDerivAt g (w x) x)
    (hw' : ∀ x∈Ioo l r, HasDerivAt w (-P.delta • g x) x)
    (h0 : f o=g o) (h1 : v o=w o) :
    ∀ x∈Icc l r, f x=g x ∧ v x=w x := by
  intro x hx
  obtain ⟨hfx,hvx⟩ := P.representation_on_closed_interval hlr ho f v hf hv hf' hv' x hx
  obtain ⟨hgx,hwx⟩ := P.representation_on_closed_interval hlr ho g w hg hw hg' hw' x hx
  exact ⟨by rw [hfx,hgx,h0,h1], by rw [hvx,hwx,h0,h1]⟩


end PropagationProfile
end QuantumTunneling
