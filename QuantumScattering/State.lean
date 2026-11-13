/-
Copyright (c) 2026 Chengyuan AI Lab. Released under Apache 2.0.
F1 DEVELOPMENT CANDIDATE. Not compiled in this authoring environment.
A physical state contains the function value and its spatial derivative.
The framework never uses the product norm of ℂ × ℂ as a spatial distance.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Basic.ExistsUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Piecewise

noncomputable section
namespace QuantumScattering

@[ext] structure State where
  value : ℂ
  slope : ℂ

def absSq (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

def fluxForm (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

def State.flux (y : State) : ℝ := fluxForm y.value y.slope

/-- This is the actual derivative, not a freely assigned velocity field. -/
def current (hbar mass : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (hbar / mass) * fluxForm (f x) (deriv f x)

lemma absSq_nonneg (z : ℂ) : 0 ≤ absSq z := by unfold absSq; positivity
@[simp] lemma absSq_zero : absSq (0 : ℂ) = 0 := by simp [absSq]
@[simp] lemma absSq_one : absSq (1 : ℂ) = 1 := by norm_num [absSq]
lemma absSq_eq_norm_sq (z : ℂ) : absSq z = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp [absSq, Complex.normSq_apply, pow_two]
lemma absSq_mul (z w : ℂ) : absSq (z*w) = absSq z * absSq w := by
  simp only [absSq, Complex.mul_re, Complex.mul_im]; ring
lemma absSq_div (z w : ℂ) : absSq (z/w) = absSq z / absSq w := by
  simp only [absSq_eq_norm_sq, norm_div, div_pow]
@[simp] lemma absSq_star (z : ℂ) : absSq (star z) = absSq z := by
  simp [absSq]
@[simp] lemma absSq_neg (z : ℂ) : absSq (-z) = absSq z := by simp [absSq]
lemma absSq_eq_zero_iff (z : ℂ) : absSq z = 0 ↔ z = 0 := by
  rw [absSq_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
lemma star_mul_self (z : ℂ) : star z*z = (absSq z : ℂ) := by
  rw [mul_comm]
  simpa [absSq, Complex.normSq_apply, pow_two] using Complex.mul_conj z
lemma mul_star_self (z : ℂ) : z*star z = (absSq z : ℂ) := by
  rw [mul_comm, star_mul_self]
lemma fluxForm_eq_im (z w : ℂ) : fluxForm z w = (star z*w).im := by
  simp [fluxForm, Complex.mul_im]; ring

/-- Flux conservation is local and needs only a real ODE coefficient at x.
No constant-potential or rectangular-barrier hypothesis is used. -/
lemma hasDerivAt_flux_zero (f v : ℝ → ℂ) (x δ : ℝ)
    (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-(δ : ℂ) * f x) x) :
    HasDerivAt (fun t => fluxForm (f t) (v t)) 0 x := by
  have hfr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hfi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hvr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hv
  have hvi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hv
  have h := (hfr.mul hvi).sub (hfi.mul hvr)
  change HasDerivAt (fun t => (f t).re * (v t).im - (f t).im * (v t).re) 0 x
  convert h using 1
  · rfl
  · simp [Function.comp_def, Complex.mul_re, Complex.mul_im]
    ring

/-- Global Schrödinger equation semantics, with only finitely many excluded jumps.
Neither existence, uniqueness nor flux conservation is assumed in this predicate. -/
structure ClassicalState (δ : ℝ → ℝ) (jumps : Set ℝ)
    (f v : ℝ → ℂ) : Prop where
  derivative : ∀ x, HasDerivAt f (v x) x
  continuous_slope : Continuous v
  equation : ∀ x, x ∉ jumps → HasDerivAt v (-(δ x : ℂ) * f x) x

lemma ClassicalState.deriv_eq {δ jumps f v} (h : ClassicalState δ jumps f v) :
    deriv f = v := funext fun x => (h.derivative x).deriv

lemma ClassicalState.C1 {δ jumps f v} (h : ClassicalState δ jumps f v) :
    ContDiff ℝ 1 f := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (h.derivative x).differentiableAt, ?_⟩
  rw [h.deriv_eq]
  exact h.continuous_slope

lemma ClassicalState.second_order {δ jumps f v} (h : ClassicalState δ jumps f v)
    (x : ℝ) (hx : x ∉ jumps) : deriv (deriv f) x = -(δ x : ℂ) * f x := by
  rw [h.deriv_eq]
  exact (h.equation x hx).deriv

end QuantumScattering
