/- F2 Lean 4.35.0. Generated from canonical modules. -/
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

/- MODULE State -/
/-
Copyright (c) 2026 Chengyuan AI Lab. Released under Apache 2.0.
F1 DEVELOPMENT CANDIDATE. Not compiled in this authoring environment.
A physical state contains the function value and its spatial derivative.
The framework never uses the product norm of ℂ × ℂ as a spatial distance.
-/

noncomputable section Bundle_State
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

end Bundle_State

/- MODULE RealTransfer -/
/- F1 candidate. Real state propagation, independent of potential shape. -/

noncomputable section Bundle_RealTransfer
namespace QuantumScattering

/-- A real two-dimensional transfer map with unit determinant. Concrete layer
constructors PROVE the last field; a user never supplies scattering unitarity. -/
@[ext] structure RealTransfer where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  unitDet : a*d-b*c=1

namespace RealTransfer

def identity : RealTransfer := ⟨1,0,0,1,by norm_num⟩

def act (P : RealTransfer) (y : State) : State :=
  ⟨(P.a : ℂ)*y.value + (P.b : ℂ)*y.slope,
   (P.c : ℂ)*y.value + (P.d : ℂ)*y.slope⟩

/-- `Q.after P` traverses P FIRST, Q SECOND, so its matrix is Q*P. -/
def after (Q P : RealTransfer) : RealTransfer where
  a := Q.a*P.a+Q.b*P.c
  b := Q.a*P.b+Q.b*P.d
  c := Q.c*P.a+Q.d*P.c
  d := Q.c*P.b+Q.d*P.d
  unitDet := by
    calc
      _ = (Q.a*Q.d-Q.b*Q.c)*(P.a*P.d-P.b*P.c) := by ring
      _ = 1 := by rw [Q.unitDet,P.unitDet]; norm_num

def reverse (P : RealTransfer) : RealTransfer :=
  ⟨P.d,-P.b,-P.c,P.a,by nlinarith [P.unitDet]⟩

def matrix (P : RealTransfer) : Matrix (Fin 2) (Fin 2) ℝ := !![P.a,P.b;P.c,P.d]

lemma matrix_det (P : RealTransfer) : P.matrix.det=1 := by
  simpa [matrix,Matrix.det_fin_two] using P.unitDet

@[simp] lemma identity_act (y : State) : identity.act y = y := by
  ext <;> simp [identity,act]

lemma after_act (Q P : RealTransfer) (y : State) :
    (Q.after P).act y = Q.act (P.act y) := by
  ext <;> simp [after,act] <;> ring

lemma after_assoc (R Q P : RealTransfer) :
    R.after (Q.after P) = (R.after Q).after P := by
  ext <;> simp [after] <;> ring

@[simp] lemma identity_after (P : RealTransfer) : identity.after P = P := by
  ext <;> simp [identity,after]
@[simp] lemma after_identity (P : RealTransfer) : P.after identity = P := by
  ext <;> simp [identity,after]

lemma reverse_after (P : RealTransfer) : P.reverse.after P = identity := by
  ext <;> simp [reverse,after,identity] <;> nlinarith [P.unitDet]

lemma after_reverse (P : RealTransfer) : P.after P.reverse = identity := by
  ext <;> simp [reverse,after,identity] <;> nlinarith [P.unitDet]

lemma act_injective (P : RealTransfer) : Function.Injective P.act := by
  intro y z h
  have hh := congrArg P.reverse.act h
  simpa only [← after_act,reverse_after,identity_act] using hh

/-- Symplectic/flux identity obtained by direct real algebra. -/
theorem flux_preserved (P : RealTransfer) (y : State) : (P.act y).flux=y.flux := by
  calc
    (P.act y).flux = (P.a*P.d-P.b*P.c)*y.flux := by
      simp [act,State.flux,fluxForm,Complex.mul_re,Complex.mul_im] <;> ring
    _ = y.flux := by rw [P.unitDet,one_mul]

/-- Arbitrarily long ordered finite compositions, not fixed-size examples. -/
def chain : List RealTransfer → RealTransfer
  | [] => identity
  | P::rest => (chain rest).after P

lemma chain_append (xs ys : List RealTransfer) :
    chain (xs++ys) = (chain ys).after (chain xs) := by
  induction xs with
  | nil => simp [chain]
  | cons p rest ih => simp [chain,ih,after_assoc]

theorem chain_flux (xs : List RealTransfer) (y : State) :
    ((chain xs).act y).flux=y.flux := (chain xs).flux_preserved y

end RealTransfer
end QuantumScattering

end Bundle_RealTransfer

/- MODULE LocalFlow -/
/- F1 candidate. Elementary local fundamental solutions extracted from Q4's
profile interface. Unlike the old physical constructor, delta can be ANY real,
so wells, barriers, free intervals and exact thresholds use the same code.
No claim of Lean verification is inherited from Q2. -/

noncomputable section Bundle_LocalFlow
namespace QuantumScattering

/-- Real fundamental solutions of u'' = -delta*u with fixed initial data. -/
structure LocalProfile where
  delta : ℝ
  C : ℝ → ℝ
  S : ℝ → ℝ
  C_zero : C 0 = 1
  S_zero : S 0 = 0
  C_neg : ∀ x, C (-x) = C x
  S_neg : ∀ x, S (-x) = -S x
  C_deriv : ∀ x, HasDerivAt C (-delta * S x) x
  S_deriv : ∀ x, HasDerivAt S (C x) x
  invariant : ∀ x, C x ^ 2 + delta * S x ^ 2 = 1

namespace LocalProfile

/-- Exact threshold: no division by a vanishing interior wave number. -/
def critical : LocalProfile where
  delta := 0
  C := fun _ => 1
  S := fun x => x
  C_zero := rfl
  S_zero := rfl
  C_neg := fun _ => rfl
  S_neg := fun _ => rfl
  C_deriv := by intro x; simpa using (hasDerivAt_const x (1 : ℝ))
  S_deriv := by intro x; exact hasDerivAt_id x
  invariant := by intro x; norm_num

/-- E > V: cosine and the normalized sine, not a singular threshold formula. -/
def oscillatory (q : ℝ) (hq : 0 < q) : LocalProfile where
  delta := q ^ 2
  C := fun x => Real.cos (q * x)
  S := fun x => Real.sin (q * x) / q
  C_zero := by simp
  S_zero := by simp
  C_neg := by intro x; simp [mul_neg]
  S_neg := by intro x; simp [mul_neg, neg_div]
  C_deriv := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => q * y) q x := by
      simpa using (hasDerivAt_id x).const_mul q
    convert hp.cos using 1 <;> field_simp [ne_of_gt hq] <;> ring
  S_deriv := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => q * y) q x := by
      simpa using (hasDerivAt_id x).const_mul q
    convert hp.sin.div_const q using 1 <;> field_simp [ne_of_gt hq] <;> ring
  invariant := by
    intro x
    calc
      Real.cos (q*x)^2 + q^2 * (Real.sin (q*x)/q)^2 =
          Real.cos (q*x)^2 + Real.sin (q*x)^2 := by
        field_simp [ne_of_gt hq] <;> ring
      _ = 1 := by simpa [add_comm] using Real.sin_sq_add_cos_sq (q*x)

/-- 0 < E < V: both evanescent modes occur through cosh and sinh/kappa. -/
def evanescent (κ : ℝ) (hκ : 0 < κ) : LocalProfile where
  delta := -(κ ^ 2)
  C := fun x => Real.cosh (κ * x)
  S := fun x => Real.sinh (κ * x) / κ
  C_zero := by simp
  S_zero := by simp
  C_neg := by intro x; simp [mul_neg]
  S_neg := by intro x; simp [mul_neg, neg_div]
  C_deriv := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => κ * y) κ x := by
      simpa using (hasDerivAt_id x).const_mul κ
    convert hp.cosh using 1 <;> field_simp [ne_of_gt hκ] <;> ring
  S_deriv := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => κ * y) κ x := by
      simpa using (hasDerivAt_id x).const_mul κ
    convert hp.sinh.div_const κ using 1 <;> field_simp [ne_of_gt hκ] <;> ring
  invariant := by
    intro x
    calc
      Real.cosh (κ*x)^2 + -(κ^2) * (Real.sinh (κ*x)/κ)^2 =
          Real.cosh (κ*x)^2 - Real.sinh (κ*x)^2 := by
        field_simp [ne_of_gt hκ] <;> ring
      _ = 1 := Real.cosh_sq_sub_sinh_sq (κ*x)

end LocalProfile

namespace LocalProfile

/-- Total constructor with a separate threshold branch; never divides by zero. -/
def ofDelta (δ : ℝ) : LocalProfile :=
  if h : δ < 0 then evanescent (Real.sqrt (-δ)) (Real.sqrt_pos.2 (by linarith))
  else if h0 : δ = 0 then critical
  else oscillatory (Real.sqrt δ) (Real.sqrt_pos.2 (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h0)))

lemma ofDelta_delta (δ : ℝ) : (ofDelta δ).delta = δ := by
  unfold ofDelta
  split_ifs with hn hz
  · dsimp [evanescent]
    rw [Real.sq_sqrt (by linarith : 0 ≤ -δ)]
    ring
  · simpa [critical] using hz.symm
  · dsimp [oscillatory]
    exact Real.sq_sqrt (le_of_not_gt hn)

/-- The map of (value, derivative) across a signed spatial displacement. -/
def transfer (P : LocalProfile) (x : ℝ) : RealTransfer where
  a := P.C x
  b := P.S x
  c := -P.delta * P.S x
  d := P.C x
  unitDet := by nlinarith [P.invariant x]

def flow (P : LocalProfile) (y : State) (x : ℝ) : State := (P.transfer x).act y

@[simp] lemma transfer_zero (P : LocalProfile) : P.transfer 0=RealTransfer.identity := by
  ext <;> simp [transfer,P.C_zero,P.S_zero,RealTransfer.identity]

@[simp] lemma flow_zero (P : LocalProfile) (y : State) : P.flow y 0=y := by
  simp [flow]

lemma transfer_neg (P : LocalProfile) (x : ℝ) :
    P.transfer (-x)=(P.transfer x).reverse := by
  ext <;> simp [transfer,RealTransfer.reverse,P.C_neg,P.S_neg] <;> ring

lemma hasDerivAt_value (P : LocalProfile) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (P.flow y t).value) (P.flow y x).slope x := by
  have h := ((P.C_deriv x).ofReal_comp.mul_const y.value).add
    ((P.S_deriv x).ofReal_comp.mul_const y.slope)
  convert h using 1
  · funext t
    simp [flow, transfer, RealTransfer.act, Pi.add_apply] <;> ring
  · simp [flow, transfer, RealTransfer.act] <;> ring

lemma hasDerivAt_slope (P : LocalProfile) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (P.flow y t).slope)
      (-(P.delta : ℂ)*(P.flow y x).value) x := by
  have h := (((P.S_deriv x).ofReal_comp.const_mul (-(P.delta : ℂ))).mul_const y.value).add
    ((P.C_deriv x).ofReal_comp.mul_const y.slope)
  convert h using 1
  · funext t
    simp [flow, transfer, RealTransfer.act, Pi.add_apply] <;> ring
  · simp [flow, transfer, RealTransfer.act] <;> ring

lemma second_deriv (P : LocalProfile) (y : State) (x : ℝ) :
    deriv (deriv (fun t => (P.flow y t).value)) x =
      -(P.delta : ℂ)*(P.flow y x).value := by
  have hd : deriv (fun t => (P.flow y t).value) = fun t => (P.flow y t).slope :=
    funext fun t => (P.hasDerivAt_value y t).deriv
  rw [hd]
  exact (P.hasDerivAt_slope y x).deriv

lemma continuous_value (P : LocalProfile) (y : State) :
    Continuous (fun t => (P.flow y t).value) :=
  (show Differentiable ℝ (fun t => (P.flow y t).value) from
    fun t => (P.hasDerivAt_value y t).differentiableAt).continuous

lemma continuous_slope (P : LocalProfile) (y : State) :
    Continuous (fun t => (P.flow y t).slope) :=
  (show Differentiable ℝ (fun t => (P.flow y t).slope) from
    fun t => (P.hasDerivAt_slope y t).differentiableAt).continuous

lemma flux_preserved (P : LocalProfile) (y : State) (x : ℝ) :
    (P.flow y x).flux=y.flux := (P.transfer x).flux_preserved y

/-- Real matrix representation of a real local ODE, with actual derivatives. -/
theorem local_cauchy_solution (δ : ℝ) (y : State) :
    (ofDelta δ).flow y 0=y ∧
    (∀ x, HasDerivAt (fun t => ((ofDelta δ).flow y t).value)
      ((ofDelta δ).flow y x).slope x) ∧
    (∀ x, HasDerivAt (fun t => ((ofDelta δ).flow y t).slope)
      (-(δ : ℂ)*((ofDelta δ).flow y x).value) x) ∧
    (∀ x, ((ofDelta δ).flow y x).flux=y.flux) := by
  refine ⟨flow_zero _ _,hasDerivAt_value _ _,?_,flux_preserved _ _⟩
  intro x
  simpa only [ofDelta_delta] using (ofDelta δ).hasDerivAt_slope y x

end LocalProfile
end QuantumScattering

end Bundle_LocalFlow

/- MODULE Layers -/
/- F1 candidate. Finite REAL layers: no nonnegativity hypothesis on heights. -/

noncomputable section Bundle_Layers
namespace QuantumScattering

/-- A spectral segment. A signed delta represents oscillatory, linear or
exponential behavior without restricting the incident energy relative to V. -/
structure Layer where
  delta : ℝ
  width : ℝ
  width_pos : 0 < width

namespace Layer

def profile (s : Layer) : LocalProfile := LocalProfile.ofDelta s.delta

def transfer (s : Layer) : RealTransfer := s.profile.transfer s.width

def flow (s : Layer) (y : State) (x : ℝ) : State := s.profile.flow y x

@[simp] lemma delta_profile (s : Layer) : s.profile.delta=s.delta :=
  LocalProfile.ofDelta_delta s.delta
@[simp] lemma flow_zero (s : Layer) (y : State) : s.flow y 0=y :=
  s.profile.flow_zero y
lemma endpoint (s : Layer) (y : State) : s.flow y s.width=s.transfer.act y := rfl
lemma hasDerivAt_value (s : Layer) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (s.flow y t).value) (s.flow y x).slope x :=
  s.profile.hasDerivAt_value y x
lemma hasDerivAt_slope (s : Layer) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (s.flow y t).slope) (-(s.delta : ℂ)*(s.flow y x).value) x := by
  simpa only [flow, delta_profile] using s.profile.hasDerivAt_slope y x
lemma flux_preserved (s : Layer) (y : State) (x : ℝ) :
    (s.flow y x).flux=y.flux := s.profile.flux_preserved y x
end Layer

abbrev Stack := List Layer

namespace Stack

def width : Stack → ℝ
  | [] => 0
  | s::rest => s.width+width rest

def transfer : Stack → RealTransfer
  | [] => RealTransfer.identity
  | s::rest => (transfer rest).after s.transfer

def exitState : Stack → State → State
  | [],y => y
  | s::rest,y => exitState rest (s.transfer.act y)

lemma width_nonneg (xs : Stack) : 0 ≤ width xs := by
  induction xs with
  | nil => simp [width]
  | cons s rest ih => exact add_nonneg (le_of_lt s.width_pos) ih

lemma width_append (xs ys : Stack) : width (xs++ys)=width xs+width ys := by
  induction xs with
  | nil => simp [width]
  | cons s rest ih => simp [width,ih,add_assoc]

lemma transfer_append (xs ys : Stack) :
    transfer (xs++ys)=(transfer ys).after (transfer xs) := by
  induction xs with
  | nil => simp [transfer]
  | cons s rest ih => simp [transfer,ih,RealTransfer.after_assoc]

lemma exitState_eq_transfer (xs : Stack) (y : State) :
    exitState xs y=(transfer xs).act y := by
  induction xs generalizing y with
  | nil => simp [exitState,transfer]
  | cons s rest ih => simp [exitState,transfer,ih,RealTransfer.after_act]

theorem exit_flux (xs : Stack) (y : State) : (exitState xs y).flux=y.flux := by
  rw [exitState_eq_transfer]
  exact (transfer xs).flux_preserved y

/-- New blocks compose by proof reuse, not re-solving all previous coefficients. -/
theorem compositional_contract (xs ys : Stack) (y : State) :
    exitState (xs++ys) y = exitState ys (exitState xs y) ∧
    (exitState (xs++ys) y).flux=y.flux := by
  constructor
  · simp only [exitState_eq_transfer,transfer_append,RealTransfer.after_act]
  · exact exit_flux _ _

end Stack
end QuantumScattering

end Bundle_Layers

/- MODULE Channels -/
/- F1 candidate. Flux-normalized channels for unequal exterior wave numbers.
The normalization is essential: raw wave amplitudes do not have a Euclidean
unitary S matrix when k_left and k_right differ. Constant mass is retained. -/

noncomputable section Bundle_Channels
namespace QuantumScattering

namespace RealTransfer

def scale (u : ℝ) (hu : u ≠ 0) : RealTransfer :=
  ⟨u,0,0,u⁻¹,by simp [hu]⟩
end RealTransfer

@[ext] structure Modes where
  forward : ℂ
  backward : ℂ

def Modes.flux (x : Modes) : ℝ := absSq x.forward-absSq x.backward

def encodeCanonical (x : Modes) : State :=
  ⟨x.forward+x.backward,Complex.I*(x.forward-x.backward)⟩

def decodeCanonical (y : State) : Modes :=
  ⟨(y.value-Complex.I*y.slope)/2,(y.value+Complex.I*y.slope)/2⟩

@[simp] lemma decode_encode (x : Modes) : decodeCanonical (encodeCanonical x)=x := by
  ext <;> apply Complex.ext <;>
    simp [decodeCanonical,encodeCanonical,Complex.mul_re,Complex.mul_im] <;> ring

@[simp] lemma encode_decode (y : State) : encodeCanonical (decodeCanonical y)=y := by
  ext <;> apply Complex.ext <;>
    simp [decodeCanonical,encodeCanonical,Complex.mul_re,Complex.mul_im] <;> ring

lemma encodeCanonical_injective : Function.Injective encodeCanonical := by
  intro x y h
  simpa using congrArg decodeCanonical h

lemma encodeCanonical_flux (x : Modes) : (encodeCanonical x).flux=x.flux := by
  simp [encodeCanonical,State.flux,Modes.flux,fluxForm,absSq,
    Complex.mul_re,Complex.mul_im] <;> ring

/-- An open asymptotic propagation channel. Interior thresholds remain allowed;
exterior k=0 or closed channels need a different asymptotic scattering space. -/
structure Port where
  k : ℝ
  positive : 0 < k

namespace Port

def root (p : Port) : ℝ := Real.sqrt p.k
lemma root_pos (p : Port) : 0 < p.root := Real.sqrt_pos.2 p.positive
lemma root_sq (p : Port) : p.root^2=p.k := Real.sq_sqrt (le_of_lt p.positive)

def normalizer (p : Port) : RealTransfer := RealTransfer.scale p.root (ne_of_gt p.root_pos)

def encode (p : Port) (x : Modes) : State := p.normalizer.reverse.act (encodeCanonical x)

def decode (p : Port) (y : State) : Modes := decodeCanonical (p.normalizer.act y)

@[simp] lemma decode_encode (p : Port) (x : Modes) : p.decode (p.encode x)=x := by
  simp only [decode,encode,← RealTransfer.after_act,RealTransfer.after_reverse,
    RealTransfer.identity_act,QuantumScattering.decode_encode]

@[simp] lemma encode_decode (p : Port) (y : State) : p.encode (p.decode y)=y := by
  simp only [decode,encode,QuantumScattering.encode_decode,← RealTransfer.after_act,
    RealTransfer.reverse_after,RealTransfer.identity_act]

lemma encode_injective (p : Port) : Function.Injective p.encode := by
  intro x y h
  simpa using congrArg p.decode h

/-- Each unit mode carries reduced current one, independently of the lead k. -/
theorem encode_flux (p : Port) (x : Modes) : (p.encode x).flux=x.flux := by
  rw [encode,RealTransfer.flux_preserved,encodeCanonical_flux]

lemma encode_value (p : Port) (x : Modes) :
    (p.encode x).value=(x.forward+x.backward)/(p.root : ℂ) := by
  simp [encode,normalizer,RealTransfer.scale,RealTransfer.reverse,
    RealTransfer.act,encodeCanonical,div_eq_mul_inv]
  ring

lemma encode_slope (p : Port) (x : Modes) :
    (p.encode x).slope=(p.root : ℂ)*Complex.I*(x.forward-x.backward) := by
  simp [encode,normalizer,RealTransfer.scale,RealTransfer.reverse,
    RealTransfer.act,encodeCanonical]
  ring

end Port

/-- Coefficient transfer in the forward spatial direction. This structure does
NOT assume mirror symmetry or a purely imaginary off-diagonal coefficient. -/
structure ChannelTransfer where
  alpha : ℂ
  beta : ℂ
  balance : absSq alpha-absSq beta=1

namespace ChannelTransfer

def fromReal (P : RealTransfer) : ChannelTransfer where
  alpha := ⟨(P.a+P.d)/2,(P.b-P.c)/2⟩
  beta := ⟨(P.a-P.d)/2,(-P.b-P.c)/2⟩
  balance := by
    change ((P.a+P.d)/2)^2+((P.b-P.c)/2)^2-
      (((P.a-P.d)/2)^2+((-P.b-P.c)/2)^2)=1
    nlinarith [P.unitDet]

def act (M : ChannelTransfer) (x : Modes) : Modes :=
  ⟨M.alpha*x.forward+M.beta*x.backward,
    star M.beta*x.forward+star M.alpha*x.backward⟩

lemma alpha_ne_zero (M : ChannelTransfer) : M.alpha ≠ 0 := by
  intro h
  have hb := M.balance
  rw [h,absSq_zero] at hb
  linarith [absSq_nonneg M.beta]

lemma star_alpha_ne_zero (M : ChannelTransfer) : star M.alpha ≠ 0 := by
  intro h
  apply M.alpha_ne_zero
  simpa using congrArg star h

lemma complex_balance (M : ChannelTransfer) :
    M.alpha*star M.alpha-M.beta*star M.beta=1 := by
  rw [mul_star_self,mul_star_self,← Complex.ofReal_sub]
  exact_mod_cast M.balance

/-- The channel structure is derived from the real transfer map, rather than
postulated independently of the differential equation representation. -/
theorem fromReal_action (P : RealTransfer) (x : Modes) :
    encodeCanonical ((fromReal P).act x)=P.act (encodeCanonical x) := by
  ext <;> apply Complex.ext <;>
    simp [encodeCanonical,act,fromReal,RealTransfer.act,
      Complex.mul_re,Complex.mul_im] <;> ring

theorem flux_preserved (M : ChannelTransfer) (x : Modes) : (M.act x).flux=x.flux := by
  calc
    (M.act x).flux=(absSq M.alpha-absSq M.beta)*x.flux := by
      simp [act,Modes.flux,absSq,Complex.mul_re,Complex.mul_im] <;> ring
    _ = x.flux := by rw [M.balance,one_mul]

end ChannelTransfer

/-- A change of normalized channel basis on each side of a real transfer. -/
def channelTransfer (left right : Port) (P : RealTransfer) : ChannelTransfer :=
  ChannelTransfer.fromReal (right.normalizer.after (P.after left.normalizer.reverse))

theorem channelTransfer_action (left right : Port) (P : RealTransfer) (x : Modes) :
    right.encode ((channelTransfer left right P).act x)=P.act (left.encode x) := by
  unfold channelTransfer Port.encode
  rw [ChannelTransfer.fromReal_action]
  simp only [RealTransfer.after_act]
  rw [← RealTransfer.after_act,RealTransfer.reverse_after,RealTransfer.identity_act]

end QuantumScattering

end Bundle_Channels

/- MODULE Scattering -/
/- F1 candidate. A general reciprocal two-port S matrix: rL and rR need NOT
be equal as complex numbers. All quantities use the boundary-phase convention
and unit-flux normalization fixed in Channels.lean. -/

noncomputable section Bundle_Scattering
open scoped BigOperators
namespace QuantumScattering
namespace ChannelTransfer

def t (M : ChannelTransfer) : ℂ := 1/star M.alpha
def rLeft (M : ChannelTransfer) : ℂ := -star M.beta/star M.alpha
def rRight (M : ChannelTransfer) : ℂ := M.beta/star M.alpha

def outgoing (M : ChannelTransfer) (iL iR : ℂ) : ℂ × ℂ :=
  (M.rLeft*iL+M.t*iR,M.t*iL+M.rRight*iR)

/-- The outgoing pair actually solves the transfer problem. -/
theorem outgoing_solves (M : ChannelTransfer) (iL iR : ℂ) :
    M.act ⟨iL,(M.outgoing iL iR).1⟩=⟨(M.outgoing iL iR).2,iR⟩ := by
  ext
  · dsimp [act,outgoing,rLeft,rRight,t]
    field_simp [M.star_alpha_ne_zero, show (starRingEnd ℂ) M.alpha ≠ 0 from M.star_alpha_ne_zero]
    simp only [starRingEnd_apply]
    linear_combination iL * M.complex_balance
  · dsimp [act,outgoing,rLeft,rRight,t]
    field_simp [M.star_alpha_ne_zero, show (starRingEnd ℂ) M.alpha ≠ 0 from M.star_alpha_ne_zero]
    ring

/-- Uniqueness at the two boundaries, without supplying any outgoing data. -/
theorem outgoing_unique (M : ChannelTransfer) (iL iR oL oR : ℂ)
    (h : M.act ⟨iL,oL⟩=⟨oR,iR⟩) : (oL,oR)=M.outgoing iL iR := by
  have h2 := congrArg Modes.backward h
  change star M.beta*iL+star M.alpha*oL=iR at h2
  have hl : oL=(M.outgoing iL iR).1 := by
    dsimp [outgoing,rLeft,t]
    field_simp [M.star_alpha_ne_zero, show (starRingEnd ℂ) M.alpha ≠ 0 from M.star_alpha_ne_zero]
    simp only [starRingEnd_apply]
    linear_combination h2
  apply Prod.ext
  · exact hl
  · have h1 := congrArg Modes.forward h
    have he := congrArg Modes.forward (M.outgoing_solves iL iR)
    change M.alpha*iL+M.beta*oL=oR at h1
    change M.alpha*iL+M.beta*(M.outgoing iL iR).1=(M.outgoing iL iR).2 at he
    rw [hl] at h1
    exact h1.symm.trans he

theorem existsUnique_outgoing (M : ChannelTransfer) (iL iR : ℂ) :
    ∃! o : ℂ × ℂ, M.act ⟨iL,o.1⟩=⟨o.2,iR⟩ := by
  refine ⟨M.outgoing iL iR,M.outgoing_solves iL iR,?_⟩
  intro o h
  exact M.outgoing_unique iL iR o.1 o.2 h

def transmission (M : ChannelTransfer) : ℝ := absSq M.t
def reflectionLeft (M : ChannelTransfer) : ℝ := absSq M.rLeft
def reflectionRight (M : ChannelTransfer) : ℝ := absSq M.rRight

lemma transmission_formula (M : ChannelTransfer) :
    M.transmission=1/absSq M.alpha := by
  unfold transmission t
  rw [absSq_div, absSq_one, absSq_star]

lemma reflection_formulas (M : ChannelTransfer) :
    M.reflectionLeft=absSq M.beta/absSq M.alpha ∧
    M.reflectionRight=absSq M.beta/absSq M.alpha := by
  simp only [reflectionLeft, reflectionRight, rLeft, rRight, absSq_div, absSq_neg, absSq_star, and_self]

lemma alpha_absSq_pos (M : ChannelTransfer) : 0 < absSq M.alpha := by
  linarith [M.balance,absSq_nonneg M.beta]

lemma transmission_positive (M : ChannelTransfer) : 0 < M.transmission := by
  rw [M.transmission_formula]
  exact div_pos (by norm_num) M.alpha_absSq_pos

lemma probability_conservation (M : ChannelTransfer) :
    M.reflectionLeft+M.transmission=1 ∧ M.reflectionRight+M.transmission=1 := by
  rw [M.reflection_formulas.1,M.reflection_formulas.2,M.transmission_formula]
  have h : absSq M.beta+1=absSq M.alpha := by linarith [M.balance]
  constructor <;> rw [← add_div,h,div_self (ne_of_gt M.alpha_absSq_pos)]

lemma equal_reflection_probabilities (M : ChannelTransfer) :
    M.reflectionLeft=M.reflectionRight := by rw [M.reflection_formulas.1,M.reflection_formulas.2]

/-- General perfect-transmission criterion. No single-barrier sin(qa) criterion
is incorrectly reused for an asymmetric multi-layer system. -/
theorem transparent_iff (M : ChannelTransfer) : M.transmission=1 ↔ M.beta=0 := by
  rw [M.transmission_formula]
  constructor
  · intro h
    have ha : absSq M.alpha=1 := by
      have hx := (div_eq_iff (ne_of_gt M.alpha_absSq_pos)).mp h
      linarith
    apply (absSq_eq_zero_iff M.beta).mp
    linarith [M.balance]
  · intro h
    have ha : absSq M.alpha=1 := by simpa [h] using M.balance
    simp [ha]

lemma diagonal_left (M : ChannelTransfer) :
    star M.rLeft*M.rLeft+star M.t*M.t=1 := by
  rw [star_mul_self,star_mul_self,← Complex.ofReal_add]
  exact_mod_cast M.probability_conservation.1

lemma diagonal_right (M : ChannelTransfer) :
    star M.rRight*M.rRight+star M.t*M.t=1 := by
  rw [star_mul_self,star_mul_self,← Complex.ofReal_add]
  exact_mod_cast M.probability_conservation.2

lemma off_diagonal (M : ChannelTransfer) : star M.rLeft*M.t+star M.t*M.rRight=0 := by
  simp only [rLeft, rRight, t, star_div₀, star_neg, star_one, star_star]
  ring

lemma off_diagonal_conj (M : ChannelTransfer) : star M.t*M.rLeft+star M.rRight*M.t=0 := by
  have h := congrArg star M.off_diagonal
  simpa only [star_add, star_mul, star_star, star_zero, mul_comm] using h

def scatteringMatrix (M : ChannelTransfer) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M.rLeft,M.t;M.t,M.rRight]

/-- Reciprocity: equality of the two off-diagonal transmission amplitudes.
It does not assert equality of the two diagonal reflection amplitudes. -/
theorem symmetric_matrix (M : ChannelTransfer) : M.scatteringMatrix.transpose=M.scatteringMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scatteringMatrix,Matrix.transpose_apply]

theorem unitary_matrix (M : ChannelTransfer) :
    M.scatteringMatrix.conjTranspose*M.scatteringMatrix=1 ∧
    M.scatteringMatrix*M.scatteringMatrix.conjTranspose=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [scatteringMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two] <;>
    simp only [starRingEnd_apply] <;>
    first
    | simpa only [add_comm, mul_comm] using M.diagonal_left
    | simpa only [add_comm, mul_comm] using M.diagonal_right
    | simpa only [add_comm, mul_comm] using M.off_diagonal
    | simpa only [add_comm, mul_comm] using M.off_diagonal_conj

/-- Coherent inputs are handled through exact flux preservation; interference
terms are not discarded as if the two inputs were an incoherent mixture. -/
theorem coherent_balance (M : ChannelTransfer) (iL iR : ℂ) :
    absSq (M.outgoing iL iR).1+absSq (M.outgoing iL iR).2=absSq iL+absSq iR := by
  have hf := M.flux_preserved ⟨iL,(M.outgoing iL iR).1⟩
  rw [M.outgoing_solves] at hf
  dsimp [Modes.flux] at hf
  linarith

end ChannelTransfer
end QuantumScattering

end Bundle_Scattering

/- MODULE Splicing -/
/- Generic interface pasting, extracted from Q2 source and separated from the
rectangular physical model. F1 itself has not been compiled. -/

noncomputable section Bundle_Splicing
open Set Filter
open scoped Topology
namespace QuantumScattering

/-- Glue two globally smooth formulas along one interface. -/
def join (c : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ := if x < c then f x else g x

lemma hasDerivAt_join_boundary (c : ℝ) (f g : ℝ → ℂ) (d : ℂ)
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (heq : f c = g c) :
    HasDerivAt (join c f g) d c := by
  have hl : HasDerivWithinAt (join c f g) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx
      change x ≤ c at hx
      by_cases hxc : x < c
      · simp [join, hxc]
      · have hxc' : x = c := le_antisymm hx (le_of_not_gt hxc)
        subst x
        simpa [join] using heq.symm
    · simpa [join] using heq.symm
  have hr : HasDerivWithinAt (join c f g) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro x hx
      change c ≤ x at hx
      simp [join, not_lt.mpr hx]
    · simp [join]
  have hu : Iic c ∪ Ici c = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x c
  have h := hl.union hr
  rw [hu] at h
  exact h.hasDerivAt (by simp)

lemma hasDerivAt_join (c : ℝ) (f fD g gD : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (fD x) x) (hg : ∀ x, HasDerivAt g (gD x) x)
    (hval : f c = g c) (hder : fD c = gD c) (x : ℝ) :
    HasDerivAt (join c f g) (join c fD gD x) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · rw [join, if_pos hx]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    change y < c at hy
    simp [join, hy]
  · subst x
    have hf' : HasDerivAt f (gD c) c := (hf c).congr_deriv hder
    simpa [join] using hasDerivAt_join_boundary c f g (gD c) hf' (hg c) hval
  · rw [join, if_neg (not_lt.mpr (le_of_lt hx))]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    change c < y at hy
    simp [join, not_lt.mpr (le_of_lt hy)]

/-- Pasting continuous formulas at a point needs equality of their values.
Applied to the first-derivative formulas below, this is precisely the second
matching condition at each interface; differentiability alone is not used to
infer continuity of a derivative. -/
lemma continuous_join (c : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (heq : f c = g c) :
    Continuous (join c f g) := by
  change Continuous (fun x : ℝ => if x < c then f x else g x)
  apply continuous_if
  · intro x hx
    change x ∈ frontier (Iio c) at hx
    have hxc : x = c := by
      simpa only [frontier_Iio, mem_singleton_iff] using hx
    simpa only [hxc] using heq
  · exact hf.continuousOn
  · exact hg.continuousOn


end QuantumScattering

end Bundle_Splicing

/- MODULE StackWave -/
/- F1 candidate. Actual globally C1 waves on arbitrarily many layers.
Composition is inductive in List Layer, not a hard-coded number of regions.
Only first derivatives are glued across potential jumps. -/

noncomputable section Bundle_StackWave
open Set Filter
open scoped Topology
namespace QuantumScattering

def Port.profile (p : Port) : LocalProfile := LocalProfile.oscillatory p.k p.positive

namespace Stack

/-- Interior and right lead, extrapolated to all x for convenient pasting.
In each recursive call the origin is the left edge of the remaining stack. -/
def tail (right : Port) : Stack → State → ℝ → State
  | [],y,x => right.profile.flow y x
  | s::rest,y,x => if x < s.width then s.flow y x
      else tail right rest (s.transfer.act y) (x-s.width)

def tailCoefficient (right : Port) : Stack → ℝ → ℝ
  | [],_ => right.k^2
  | s::rest,x => if x < s.width then s.delta
      else tailCoefficient right rest (x-s.width)

def tailJumps : Stack → List ℝ
  | [] => []
  | s::rest => s.width :: (tailJumps rest).map (fun x => s.width+x)

/-- Interface at the left edge is also listed, even if the adjacent potentials
happen to agree. Excluding a redundant jump only weakens an ODE domain, not C1. -/
def jumps (xs : Stack) : Set ℝ := {x | x=0 ∨ x∈tailJumps xs}

@[simp] lemma tail_zero (right : Port) (xs : Stack) (y : State) : tail right xs y 0=y := by
  cases xs with
  | nil => simp [tail]
  | cons s rest => simp [tail,s.width_pos]

lemma tail_derivative (right : Port) (xs : Stack) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (tail right xs y t).value) (tail right xs y x).slope x := by
  induction xs generalizing y x with
  | nil => exact right.profile.hasDerivAt_value y x
  | cons s rest ih =>
    have h := hasDerivAt_join s.width
      (fun t => (s.flow y t).value) (fun t => (s.flow y t).slope)
      (fun t => (tail right rest (s.transfer.act y) (t-s.width)).value)
      (fun t => (tail right rest (s.transfer.act y) (t-s.width)).slope)
      (s.hasDerivAt_value y)
      (fun t => by
        simpa [Function.comp_def] using
          (ih (s.transfer.act y) (t-s.width)).scomp t ((hasDerivAt_id t).sub_const s.width))
      (by simp [Layer.endpoint]) (by simp [Layer.endpoint]) x
    have heq : (fun t => (tail right (s::rest) y t).value) =
        join s.width (fun t => (s.flow y t).value)
          (fun t => (tail right rest (s.transfer.act y) (t-s.width)).value) := by
      funext t
      by_cases ht : t < s.width <;> simp [tail, join, ht]
    rw [heq]
    by_cases hx : x < s.width <;> simpa [tail, join, hx] using h

lemma tail_slope_continuous (right : Port) (xs : Stack) (y : State) :
    Continuous (fun t => (tail right xs y t).slope) := by
  induction xs generalizing y with
  | nil => exact right.profile.continuous_slope y
  | cons s rest ih =>
    have heq : (fun t => (tail right (s::rest) y t).slope) =
        join s.width (fun t => (s.flow y t).slope)
          (fun t => (tail right rest (s.transfer.act y) (t-s.width)).slope) := by
      funext t
      by_cases ht : t < s.width <;> simp [tail, join, ht]
    rw [heq]
    apply continuous_join
    · exact s.profile.continuous_slope y
    · exact (ih (s.transfer.act y)).comp (continuous_id.sub continuous_const)
    · simp [Layer.endpoint]

lemma tail_slope_derivative (right : Port) (xs : Stack) (y : State)
    (x : ℝ) (hx : x∉tailJumps xs) :
    HasDerivAt (fun t => (tail right xs y t).slope)
      (-(tailCoefficient right xs x : ℂ)*(tail right xs y x).value) x := by
  induction xs generalizing y x with
  | nil => exact right.profile.hasDerivAt_slope y x
  | cons s rest ih =>
    have hne : x≠s.width := by
      intro h; apply hx; simp [tailJumps,h]
    by_cases hlt : x<s.width
    · simp only [tailCoefficient,tail,if_pos hlt]
      apply (s.hasDerivAt_slope y x).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hlt] with t ht
      simp only [tail,if_pos (show t<s.width from ht)]
    · have hgt : s.width<x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      have hrest : x-s.width∉tailJumps rest := by
        intro hm
        apply hx
        simp only [tailJumps,List.mem_cons,List.mem_map]
        right
        exact ⟨x-s.width,hm,by ring⟩
      have hd := (ih (s.transfer.act y) (x-s.width) hrest).scomp x
        ((hasDerivAt_id x).sub_const s.width)
      simp only [tailCoefficient,tail,if_neg hlt]
      apply (show HasDerivAt
        (fun t => (tail right rest (s.transfer.act y) (t-s.width)).slope)
        (-(tailCoefficient right rest (x-s.width) : ℂ)*
          (tail right rest (s.transfer.act y) (x-s.width)).value) x from by simpa [Function.comp_def] using hd).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hgt] with t ht
      simp only [tail,if_neg (not_lt.mpr (le_of_lt (show s.width<t from ht)))]

lemma tail_flux (right : Port) (xs : Stack) (y : State) (x : ℝ) :
    (tail right xs y x).flux=y.flux := by
  induction xs generalizing y x with
  | nil => exact right.profile.flux_preserved y x
  | cons s rest ih =>
    by_cases h : x<s.width
    · simpa only [tail,if_pos h] using s.flux_preserved y x
    · simp only [tail,if_neg h]
      rw [ih,s.transfer.flux_preserved]

/-- Beyond the last interface, the wave is the right free evolution of the
actual composed exit data. This is the bridge from PDE segments to transfer. -/
lemma tail_right (right : Port) (xs : Stack) (y : State) (x : ℝ)
    (hx : width xs ≤ x) :
    tail right xs y x=right.profile.flow ((transfer xs).act y) (x-width xs) := by
  induction xs generalizing y x with
  | nil => simp [tail,transfer,width]
  | cons s rest ih =>
    have hrest : width rest ≤ x-s.width := by simp only [width] at hx; linarith
    have hlt : ¬x<s.width := by have hn := width_nonneg rest; simp [width] at hx; linarith
    rw [tail,if_neg hlt,ih _ _ hrest]
    simp only [transfer,RealTransfer.after_act,width]
    congr 1
    ring

/-- The global state, including the true left lead. -/
def waveState (left right : Port) (xs : Stack) (y : State) (x : ℝ) : State :=
  if x<0 then left.profile.flow y x else tail right xs y x

def coefficient (left right : Port) (xs : Stack) (x : ℝ) : ℝ :=
  if x<0 then left.k^2 else tailCoefficient right xs x

@[simp] lemma waveState_zero (left right : Port) (xs : Stack) (y : State) :
    waveState left right xs y 0=y := by simp [waveState]

lemma wave_derivative (left right : Port) (xs : Stack) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (waveState left right xs y t).value)
      (waveState left right xs y x).slope x := by
  have h := hasDerivAt_join 0
    (fun t => (left.profile.flow y t).value) (fun t => (left.profile.flow y t).slope)
    (fun t => (tail right xs y t).value) (fun t => (tail right xs y t).slope)
    (left.profile.hasDerivAt_value y) (tail_derivative right xs y) (by simp) (by simp) x
  have heq : (fun t => (waveState left right xs y t).value) =
      join 0 (fun t => (left.profile.flow y t).value) (fun t => (tail right xs y t).value) := by
    funext t
    by_cases ht : t < 0 <;> simp [waveState, join, ht]
  rw [heq]
  by_cases hx : x < 0 <;> simpa [waveState, join, hx] using h

lemma wave_slope_continuous (left right : Port) (xs : Stack) (y : State) :
    Continuous (fun t => (waveState left right xs y t).slope) := by
  have heq : (fun t => (waveState left right xs y t).slope) =
      join 0 (fun t => (left.profile.flow y t).slope) (fun t => (tail right xs y t).slope) := by
    funext t
    by_cases ht : t < 0 <;> simp [waveState, join, ht]
  rw [heq]
  exact continuous_join 0 _ _ (left.profile.continuous_slope y)
    (tail_slope_continuous right xs y) (by simp)

lemma wave_slope_derivative (left right : Port) (xs : Stack) (y : State)
    (x : ℝ) (hx : x∉jumps xs) :
    HasDerivAt (fun t => (waveState left right xs y t).slope)
      (-(coefficient left right xs x : ℂ)*(waveState left right xs y x).value) x := by
  have h0 : x≠0 := fun h => hx (Or.inl h)
  have hj : x∉tailJumps xs := fun h => hx (Or.inr h)
  by_cases hn : x<0
  · simp only [coefficient,waveState,if_pos hn]
    apply (left.profile.hasDerivAt_slope y x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hn] with t ht
    simp only [waveState,if_pos (show t<0 from ht)]
  · have hp : 0<x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm h0)
    simp only [coefficient,waveState,if_neg hn]
    apply (tail_slope_derivative right xs y x hj).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hp] with t ht
    simp only [waveState,if_neg (not_lt.mpr (le_of_lt (show 0<t from ht)))]

theorem classical_wave (left right : Port) (xs : Stack) (y : State) :
    ClassicalState (coefficient left right xs) (jumps xs)
      (fun x => (waveState left right xs y x).value)
      (fun x => (waveState left right xs y x).slope) :=
  ⟨wave_derivative left right xs y,wave_slope_continuous left right xs y,
    wave_slope_derivative left right xs y⟩

theorem wave_flux (left right : Port) (xs : Stack) (y : State) (x : ℝ) :
    (waveState left right xs y x).flux=y.flux := by
  by_cases h : x<0
  · simpa only [waveState,if_pos h] using left.profile.flux_preserved y x
  · simpa only [waveState,if_neg h] using tail_flux right xs y x

theorem actual_current (left right : Port) (xs : Stack) (y : State)
    (hbar mass x : ℝ) :
    current hbar mass (fun t => (waveState left right xs y t).value) x=
      (hbar/mass)*y.flux := by
  unfold current
  rw [(wave_derivative left right xs y x).deriv]
  exact congrArg (fun u => (hbar/mass)*u) (wave_flux left right xs y x)

lemma waveState_exit (left right : Port) (xs : Stack) (y : State) :
    waveState left right xs y (width xs)=(transfer xs).act y := by
  rw [waveState,if_neg (not_lt.mpr (width_nonneg xs)),tail_right right xs y _ le_rfl]
  simp

end Stack
end QuantumScattering

end Bundle_StackWave

/- MODULE FiniteScattering -/
/- F1 candidate. Full explicit finite-stack wave linked to the same channel
transfer used for the scattering amplitudes. No probability ratio is defined
independently of the actual current or the state differential equation. -/

noncomputable section Bundle_FiniteScattering
namespace QuantumScattering

structure Problem where
  left : Port
  right : Port
  layers : Stack

namespace Problem

def transfer (p : Problem) : RealTransfer := Stack.transfer p.layers
def channels (p : Problem) : ChannelTransfer := channelTransfer p.left p.right p.transfer

def outgoing (p : Problem) (iL iR : ℂ) : ℂ × ℂ := p.channels.outgoing iL iR

def initial (p : Problem) (iL iR : ℂ) : State :=
  p.left.encode ⟨iL,(p.outgoing iL iR).1⟩

def state (p : Problem) (iL iR : ℂ) (x : ℝ) : State :=
  Stack.waveState p.left p.right p.layers (p.initial iL iR) x

def wave (p : Problem) (iL iR : ℂ) (x : ℝ) : ℂ := (p.state iL iR x).value
def waveD (p : Problem) (iL iR : ℂ) (x : ℝ) : ℂ := (p.state iL iR x).slope

def coefficient (p : Problem) : ℝ → ℝ := Stack.coefficient p.left p.right p.layers

def jumps (p : Problem) : Set ℝ := Stack.jumps p.layers

theorem classical (p : Problem) (iL iR : ℂ) :
    ClassicalState p.coefficient p.jumps (p.wave iL iR) (p.waveD iL iR) :=
  Stack.classical_wave p.left p.right p.layers (p.initial iL iR)

theorem C1 (p : Problem) (iL iR : ℂ) : ContDiff ℝ 1 (p.wave iL iR) :=
  (p.classical iL iR).C1

theorem second_order (p : Problem) (iL iR : ℂ) (x : ℝ) (hx : x∉p.jumps) :
    deriv (deriv (p.wave iL iR)) x=-(p.coefficient x : ℂ)*p.wave iL iR x :=
  (p.classical iL iR).second_order x hx

lemma exit_data (p : Problem) (iL iR : ℂ) :
    p.transfer.act (p.initial iL iR)=p.right.encode ⟨(p.outgoing iL iR).2,iR⟩ := by
  have h := channelTransfer_action p.left p.right p.transfer ⟨iL,(p.outgoing iL iR).1⟩
  change p.right.encode (p.channels.act ⟨iL,(p.outgoing iL iR).1⟩)=
    p.transfer.act (p.initial iL iR) at h
  simpa only [outgoing, p.channels.outgoing_solves] using h.symm

lemma left_boundary (p : Problem) (iL iR : ℂ) :
    p.left.decode (p.state iL iR 0)=⟨iL,(p.outgoing iL iR).1⟩ := by
  simp [state,initial]

lemma right_boundary (p : Problem) (iL iR : ℂ) :
    p.right.decode (p.state iL iR (Stack.width p.layers))=
      ⟨(p.outgoing iL iR).2,iR⟩ := by
  rw [state,Stack.waveState_exit]
  change p.right.decode (p.transfer.act (p.initial iL iR))=_
  rw [p.exit_data,p.right.decode_encode]

lemma left_exterior (p : Problem) (iL iR : ℂ) (x : ℝ) (hx : x<0) :
    p.state iL iR x=p.left.profile.flow (p.initial iL iR) x := by
  simp only [state,Stack.waveState,if_pos hx]

lemma right_exterior (p : Problem) (iL iR : ℂ) (x : ℝ)
    (hx : Stack.width p.layers ≤ x) :
    p.state iL iR x=p.right.profile.flow
      (p.right.encode ⟨(p.outgoing iL iR).2,iR⟩) (x-Stack.width p.layers) := by
  have h0 : 0≤x := le_trans (Stack.width_nonneg _) hx
  rw [state,Stack.waveState,if_neg (not_lt.mpr h0),Stack.tail_right _ _ _ _ hx]
  change p.right.profile.flow (p.transfer.act (p.initial iL iR)) _=_
  rw [p.exit_data]

theorem current_left (p : Problem) (iL iR : ℂ) (hbar mass x : ℝ) :
    current hbar mass (p.wave iL iR) x=
      (hbar/mass)*(absSq iL-absSq (p.outgoing iL iR).1) := by
  change current hbar mass (fun t => (p.state iL iR t).value) x = _
  change current hbar mass
    (fun t => (Stack.waveState p.left p.right p.layers (p.initial iL iR) t).value) x = _
  rw [Stack.actual_current]
  unfold initial
  rw [p.left.encode_flux]
  rfl

theorem current_right (p : Problem) (iL iR : ℂ) (hbar mass x : ℝ) :
    current hbar mass (p.wave iL iR) x=
      (hbar/mass)*(absSq (p.outgoing iL iR).2-absSq iR) := by
  rw [p.current_left]
  have h := p.channels.coherent_balance iL iR
  change absSq (p.outgoing iL iR).1+absSq (p.outgoing iL iR).2=absSq iL+absSq iR at h
  congr 1
  linarith

/-- Unlike a hard-coded barrier theorem, this has arbitrary list length and
independent positive left/right wave numbers. -/
theorem finite_stack_scattering (p : Problem) (iL iR : ℂ) :
    ClassicalState p.coefficient p.jumps (p.wave iL iR) (p.waveD iL iR) ∧
    ContDiff ℝ 1 (p.wave iL iR) ∧
    p.left.decode (p.state iL iR 0)=⟨iL,(p.outgoing iL iR).1⟩ ∧
    p.right.decode (p.state iL iR (Stack.width p.layers))=⟨(p.outgoing iL iR).2,iR⟩ ∧
    (∀ hbar mass x, current hbar mass (p.wave iL iR) x=
      (hbar/mass)*(absSq iL-absSq (p.outgoing iL iR).1)) ∧
    p.channels.scatteringMatrix.conjTranspose*p.channels.scatteringMatrix=1 ∧
    p.channels.scatteringMatrix*p.channels.scatteringMatrix.conjTranspose=1 ∧
    p.channels.scatteringMatrix.transpose=p.channels.scatteringMatrix := by
  exact ⟨p.classical iL iR,p.C1 iL iR,p.left_boundary iL iR,p.right_boundary iL iR,
    p.current_left iL iR,p.channels.unitary_matrix.1,p.channels.unitary_matrix.2,
    p.channels.symmetric_matrix⟩

end Problem
end QuantumScattering

end Bundle_FiniteScattering

/- MODULE PhysicalModel -/
/- F1 candidate. Construct the spectral model from physical data.
Real heights can be negative. Exterior levels can differ. Both exterior
channels must be open. Mass is constant throughout the system. -/

noncomputable section Bundle_PhysicalModel
namespace QuantumScattering

structure PhysicalLayer where
  height : ℝ
  width : ℝ
  width_pos : 0 < width

structure PhysicalProblem where
  hbar : ℝ
  mass : ℝ
  energy : ℝ
  leftLevel : ℝ
  rightLevel : ℝ
  layers : List PhysicalLayer
  hbar_pos : 0 < hbar
  mass_pos : 0 < mass
  left_open : leftLevel < energy
  right_open : rightLevel < energy

namespace PhysicalProblem

def delta (p : PhysicalProblem) (V : ℝ) : ℝ := 2*p.mass*(p.energy-V)/p.hbar^2

def k (p : PhysicalProblem) (V : ℝ) : ℝ := Real.sqrt (p.delta V)

lemma k_pos (p : PhysicalProblem) (V : ℝ) (hV : V<p.energy) : 0<p.k V := by
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr hV))
    (pow_pos p.hbar_pos 2)

lemma k_sq (p : PhysicalProblem) (V : ℝ) (hV : V<p.energy) : p.k V^2=p.delta V := by
  apply Real.sq_sqrt
  exact le_of_lt (div_pos (mul_pos (mul_pos (by norm_num) p.mass_pos) (sub_pos.mpr hV))
    (pow_pos p.hbar_pos 2))

def layer (p : PhysicalProblem) (s : PhysicalLayer) : Layer :=
  ⟨p.delta s.height,s.width,s.width_pos⟩

def problem (p : PhysicalProblem) : Problem where
  left := ⟨p.k p.leftLevel,p.k_pos p.leftLevel p.left_open⟩
  right := ⟨p.k p.rightLevel,p.k_pos p.rightLevel p.right_open⟩
  layers := p.layers.map p.layer

def tailPotential (rightLevel : ℝ) : List PhysicalLayer → ℝ → ℝ
  | [],_ => rightLevel
  | s::rest,x => if x<s.width then s.height else tailPotential rightLevel rest (x-s.width)

def potential (p : PhysicalProblem) (x : ℝ) : ℝ :=
  if x<0 then p.leftLevel else tailPotential p.rightLevel p.layers x

lemma tailCoefficient_eq (p : PhysicalProblem) (xs : List PhysicalLayer) (x : ℝ) :
    Stack.tailCoefficient p.problem.right (xs.map p.layer) x=
      p.delta (tailPotential p.rightLevel xs x) := by
  induction xs generalizing x with
  | nil => exact p.k_sq p.rightLevel p.right_open
  | cons s rest ih =>
    by_cases h : x<s.width
    · simp [Stack.tailCoefficient,tailPotential,layer,h]
    · simp [Stack.tailCoefficient,tailPotential,layer,h,ih]

lemma coefficient_eq (p : PhysicalProblem) (x : ℝ) :
    p.problem.coefficient x=p.delta (p.potential x) := by
  by_cases h : x<0
  · simpa [Problem.coefficient,Stack.coefficient,problem,potential,h] using
      p.k_sq p.leftLevel p.left_open
  · simpa [Problem.coefficient,Stack.coefficient,problem,potential,h] using
      p.tailCoefficient_eq p.layers x

lemma kinetic_delta (p : PhysicalProblem) (V : ℝ) :
    p.hbar^2/(2*p.mass)*p.delta V=p.energy-V := by
  unfold delta
  field_simp [ne_of_gt p.hbar_pos,ne_of_gt p.mass_pos] <;> ring

/-- Literal physical equation for arbitrary finite real layers, including any
number of exact interior thresholds. No solution is an input field. -/
theorem schrodinger (p : PhysicalProblem) (iL iR : ℂ) (x : ℝ)
    (hx : x∉p.problem.jumps) :
    -(p.hbar^2/(2*p.mass) : ℝ) • deriv (deriv (p.problem.wave iL iR)) x +
      p.potential x • p.problem.wave iL iR x =
      p.energy • p.problem.wave iL iR x := by
  rw [p.problem.second_order iL iR x hx,p.coefficient_eq]
  have hc : ((p.hbar^2/(2*p.mass) : ℝ) : ℂ)*(p.delta (p.potential x) : ℂ)=
      (p.energy : ℂ)-(p.potential x : ℂ) := by exact_mod_cast p.kinetic_delta (p.potential x)
  simp only [Complex.real_smul, Complex.ofReal_neg]
  linear_combination (p.problem.wave iL iR x)*hc

theorem full_physical_existence (p : PhysicalProblem) (iL iR : ℂ) :
    ContDiff ℝ 1 (p.problem.wave iL iR) ∧
    (∀ x, x∉p.problem.jumps →
      -(p.hbar^2/(2*p.mass) : ℝ) • deriv (deriv (p.problem.wave iL iR)) x +
      p.potential x • p.problem.wave iL iR x =
      p.energy • p.problem.wave iL iR x) ∧
    p.problem.channels.scatteringMatrix.conjTranspose*p.problem.channels.scatteringMatrix=1 :=
  ⟨p.problem.C1 iL iR,p.schrodinger iL iR,p.problem.channels.unitary_matrix.1⟩

end PhysicalProblem
end QuantumScattering

end Bundle_PhysicalModel

/- MODULE LocalUniqueness -/
/- F1 candidate. Generic Cauchy completeness, extracted from the Q5 analytic
argument and freed of the rectangular-model import dependency. -/

noncomputable section Bundle_LocalUniqueness
open Set Filter
open scoped Topology
namespace QuantumScattering

lemma constant_on_Icc_of_deriv_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {l r : ℝ} (hlr : l < r) (hf : Continuous f)
    (hd : ∀ x ∈ Ioo l r, HasDerivAt f 0 x)
    {x y : ℝ} (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) : f x = f y := by
  let m : ℝ := (l+r)/2
  have hm : m ∈ Ioo l r := by dsimp [m]; constructor <;> linarith
  have hc : ∀ z ∈ Ioo l r, f z = f m := by
    intro z hz
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo l r).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).deriv) hz hm
  have hclosed : IsClosed {z | f z = f m} := isClosed_eq hf continuous_const
  have hsub : closure (Ioo l r) ⊆ {z | f z = f m} :=
    hclosed.closure_subset_iff.mpr hc
  rw [closure_Ioo hlr.ne] at hsub
  exact (hsub hx).trans (hsub hy).symm

namespace LocalProfile
lemma continuous_C (P : LocalProfile) : Continuous P.C :=
  (show Differentiable ℝ P.C from fun x => (P.C_deriv x).differentiableAt).continuous
lemma continuous_S (P : LocalProfile) : Continuous P.S :=
  (show Differentiable ℝ P.S from fun x => (P.S_deriv x).differentiableAt).continuous

/-- Two inverse-fundamental-matrix coefficients of a possibly unknown solution. -/
def firstCoefficient (P : LocalProfile) (o : ℝ) (f v : ℝ → ℂ) (x : ℝ) : ℂ :=
  (P.C (x-o) : ℂ)*f x - (P.S (x-o) : ℂ)*v x

def secondCoefficient (P : LocalProfile) (o : ℝ) (f v : ℝ → ℂ) (x : ℝ) : ℂ :=
  (P.delta : ℂ)*(P.S (x-o) : ℂ)*f x + (P.C (x-o) : ℂ)*v x

lemma hasDerivAt_shift_C (P : LocalProfile) (o x : ℝ) :
    HasDerivAt (fun y => (P.C (y-o) : ℂ))
      ((-P.delta*P.S (x-o) : ℝ) : ℂ) x := by
  simpa [Function.comp_def] using ((P.C_deriv (x-o)).scomp x ((hasDerivAt_id x).sub_const o)).ofReal_comp

lemma hasDerivAt_shift_S (P : LocalProfile) (o x : ℝ) :
    HasDerivAt (fun y => (P.S (y-o) : ℂ)) (P.C (x-o) : ℂ) x := by
  simpa [Function.comp_def] using ((P.S_deriv (x-o)).scomp x ((hasDerivAt_id x).sub_const o)).ofReal_comp

lemma hasDerivAt_firstCoefficient_zero (P : LocalProfile) (o x : ℝ)
    (f v : ℝ → ℂ) (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-P.delta • f x) x) :
    HasDerivAt (P.firstCoefficient o f v) 0 x := by
  have h := ((P.hasDerivAt_shift_C o x).mul hf).sub
    ((P.hasDerivAt_shift_S o x).mul hv)
  convert h using 1
  · rfl
  · simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

lemma hasDerivAt_secondCoefficient_zero (P : LocalProfile) (o x : ℝ)
    (f v : ℝ → ℂ) (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-P.delta • f x) x) :
    HasDerivAt (P.secondCoefficient o f v) 0 x := by
  have h := (((P.hasDerivAt_shift_S o x).const_mul (P.delta : ℂ)).mul hf).add
    ((P.hasDerivAt_shift_C o x).mul hv)
  convert h using 1
  · rfl
  · simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

lemma reconstruct_value (P : LocalProfile) (o x : ℝ) (f v : ℝ → ℂ) :
    f x = P.firstCoefficient o f v x*(P.C (x-o) : ℂ) +
      P.secondCoefficient o f v x*(P.S (x-o) : ℂ) := by
  have hi : (P.C (x-o) : ℂ)^2 + (P.delta : ℂ)*(P.S (x-o) : ℂ)^2 = 1 := by
    exact_mod_cast P.invariant (x-o)
  calc
    f x = f x*((P.C (x-o) : ℂ)^2+(P.delta : ℂ)*(P.S (x-o) : ℂ)^2) := by rw [hi,mul_one]
    _ = _ := by unfold firstCoefficient secondCoefficient; ring

lemma reconstruct_derivative (P : LocalProfile) (o x : ℝ) (f v : ℝ → ℂ) :
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
theorem representation_on_closed_interval (P : LocalProfile)
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
theorem cauchy_unique_on_closed_interval (P : LocalProfile)
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



lemma state_representation (P : LocalProfile) {l r : ℝ} (hlr : l<r)
    (f v : ℝ → ℂ) (hf : Continuous f) (hv : Continuous v)
    (hfv : ∀ x∈Ioo l r, HasDerivAt f (v x) x)
    (hode : ∀ x∈Ioo l r, HasDerivAt v (-(P.delta : ℂ)*f x) x)
    (x : ℝ) (hx : x∈Icc l r) :
    (⟨f x,v x⟩ : State)=P.flow ⟨f l,v l⟩ (x-l) := by
  obtain ⟨h1,h2⟩ := P.representation_on_closed_interval hlr ⟨le_rfl,le_of_lt hlr⟩
    f v hf hv hfv (by intro y hy; simpa only [Complex.real_smul, Complex.ofReal_neg] using hode y hy) x hx
  apply State.ext
  · simpa [flow,transfer,RealTransfer.act,mul_comm] using h1
  · simpa [flow,transfer,RealTransfer.act,mul_comm,mul_left_comm,mul_assoc] using h2

end LocalProfile
end QuantumScattering

end Bundle_LocalUniqueness

/- MODULE StackUniqueness -/
/- F1 candidate. Arbitrary-function uniqueness across any finite layer list.
No modal ansatz is an assumption on the function to be identified. -/

noncomputable section Bundle_StackUniqueness
open Set
namespace QuantumScattering
namespace Stack

lemma tailJumps_positive (xs : Stack) (x : ℝ) (hx : x∈tailJumps xs) : 0<x := by
  induction xs generalizing x with
  | nil => simp [tailJumps] at hx
  | cons s rest ih =>
    simp only [tailJumps,List.mem_cons,List.mem_map] at hx
    rcases hx with h | ⟨y,hy,hxy⟩
    · simpa [h] using s.width_pos
    · rw [← hxy]
      exact add_pos s.width_pos (ih y hy)

lemma first_cell_no_jump (s : Layer) (rest : Stack) (x : ℝ) (hx : x<s.width) :
    x∉tailJumps (s::rest) := by
  intro h
  simp only [tailJumps,List.mem_cons,List.mem_map] at h
  rcases h with he | ⟨y,hy,he⟩
  · linarith
  · have hp := tailJumps_positive rest y hy
    linarith

/-- Positive half-line ODE hypotheses. They constrain only actual derivatives;
the representation in tail is a conclusion. -/
structure TailSolution (right : Port) (xs : Stack) (f v : ℝ→ℂ) : Prop where
  derivative : ∀ x, HasDerivAt f (v x) x
  continuous_slope : Continuous v
  equation : ∀ x, 0<x → x∉tailJumps xs →
    HasDerivAt v (-(tailCoefficient right xs x : ℂ)*f x) x

lemma TailSolution.continuous_value {right xs f v} (h : TailSolution right xs f v) :
    Continuous f := (show Differentiable ℝ f from fun x => (h.derivative x).differentiableAt).continuous

lemma TailSolution.first_cell {right s rest f v} (h : TailSolution right (s::rest) f v)
    (x : ℝ) (hx : x∈Icc 0 s.width) :
    (⟨f x,v x⟩ : State)=s.flow ⟨f 0,v 0⟩ x := by
  have hp := s.profile.state_representation s.width_pos f v h.continuous_value
    h.continuous_slope (fun y _ => h.derivative y)
    (by
      intro y hy
      have hd := h.equation y hy.1 (first_cell_no_jump s rest y hy.2)
      simpa [tailCoefficient,hy.2,Layer.delta_profile] using hd)
    x hx
  simpa [Layer.flow] using hp

lemma TailSolution.shift {right s rest f v} (h : TailSolution right (s::rest) f v) :
    TailSolution right rest (fun x => f (s.width+x)) (fun x => v (s.width+x)) := by
  refine ⟨?_,h.continuous_slope.comp (continuous_const.add continuous_id),?_⟩
  · intro x
    simpa [Function.comp_def] using (h.derivative (s.width+x)).scomp x ((hasDerivAt_id x).const_add s.width)
  · intro x hx hn
    have hnot : s.width+x∉tailJumps (s::rest) := by
      simp only [tailJumps,List.mem_cons,List.mem_map]
      rintro (he | ⟨y,hy,he⟩)
      · linarith
      · have hyx : y=x := by linarith
        exact hn (hyx ▸ hy)
    have hd := h.equation (s.width+x) (by linarith [s.width_pos]) hnot
    have hlt : ¬s.width+x<s.width := by linarith
    simp only [tailCoefficient,if_neg hlt] at hd
    have he : s.width+x-s.width=x := by ring
    rw [he] at hd
    simpa [Function.comp_def] using hd.scomp x ((hasDerivAt_id x).const_add s.width)

/-- Every arbitrary classical solution on the half-line equals the recursively
constructed wave for its own initial data. This is not merely coefficient uniqueness. -/
theorem tail_representation (right : Port) (xs : Stack) (f v : ℝ→ℂ)
    (h : TailSolution right xs f v) (x : ℝ) (hx : 0≤x) :
    (⟨f x,v x⟩ : State)=tail right xs ⟨f 0,v 0⟩ x := by
  induction xs generalizing f v x with
  | nil =>
    have he := right.profile.state_representation (l:=0) (r:=x+1) (by linarith)
      f v h.continuous_value h.continuous_slope (fun y _ => h.derivative y)
      (by intro y hy; exact h.equation y hy.1 (by simp [tailJumps]))
      x ⟨hx,by linarith⟩
    simpa [tail] using he
  | cons s rest ih =>
    have hend := h.first_cell s.width ⟨le_of_lt s.width_pos,le_rfl⟩
    by_cases hlt : x<s.width
    · rw [tail,if_pos hlt]
      exact h.first_cell x ⟨hx,le_of_lt hlt⟩
    · rw [tail,if_neg hlt]
      have hs := ih (fun z => f (s.width+z)) (fun z => v (s.width+z)) h.shift
        (x-s.width) (by linarith)
      have hx' : s.width+(x-s.width)=x := by ring
      simp only [hx',add_zero] at hs
      rw [hend] at hs
      exact hs

end Stack
namespace Problem

lemma arbitrary_tail {p : Problem} {f v : ℝ→ℂ}
    (h : ClassicalState p.coefficient p.jumps f v) :
    Stack.TailSolution p.right p.layers f v := by
  refine ⟨h.derivative,h.continuous_slope,?_⟩
  intro x hx hn
  have hj : x∉p.jumps := by
    intro hm
    rcases hm with he | he
    · linarith
    · exact hn he
  have hd := h.equation x hj
  simpa [coefficient,Stack.coefficient,not_lt.mpr (le_of_lt hx)] using hd

/-- Transfer data for an arbitrary classical solution, derived from its ODE. -/
lemma arbitrary_endpoint {p : Problem} {f v : ℝ→ℂ}
    (h : ClassicalState p.coefficient p.jumps f v) :
    (⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩ : State)=
      p.transfer.act ⟨f 0,v 0⟩ := by
  have he := Stack.tail_representation p.right p.layers f v (arbitrary_tail h)
    (Stack.width p.layers) (Stack.width_nonneg _)
  rw [Stack.tail_right _ _ _ _ le_rfl] at he
  simpa [transfer] using he

lemma arbitrary_state_representation {p : Problem} {f v : ℝ→ℂ}
    (h : ClassicalState p.coefficient p.jumps f v) (x : ℝ) :
    (⟨f x,v x⟩ : State)=Stack.waveState p.left p.right p.layers ⟨f 0,v 0⟩ x := by
  by_cases hn : x<0
  · rw [Stack.waveState,if_pos hn]
    have hf : Continuous f :=
      (show Differentiable ℝ f from fun y => (h.derivative y).differentiableAt).continuous
    obtain ⟨hv,hd⟩ := p.left.profile.representation_on_closed_interval
      (l:=x-1) (r:=0) (o:=0) (by linarith) ⟨by linarith,le_rfl⟩
      f v hf h.continuous_slope (fun y _ => h.derivative y)
      (by
        intro y hy
        have hj : y∉p.jumps := by
          intro he
          rcases he with he | he
          · exact (ne_of_lt hy.2) he
          · exact (not_lt_of_gt hy.2) (Stack.tailJumps_positive p.layers y he)
        have H := h.equation y hj
        simpa [coefficient,Stack.coefficient,hy.2,Port.profile,
          LocalProfile.oscillatory,Complex.real_smul] using H)
      x ⟨by linarith,le_of_lt hn⟩
    apply State.ext
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,mul_comm] using hv
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,
        Complex.real_smul,mul_comm,mul_left_comm,mul_assoc] using hd
  · rw [Stack.waveState,if_neg hn]
    exact Stack.tail_representation p.right p.layers f v (arbitrary_tail h) x (le_of_not_gt hn)

/-- Exact incoming channel data at the interfaces. Because the exterior ODE is
free, these are the traveling-wave coefficients throughout the exterior rays.
An asymptotic-limit formulation is deliberately a separate API, not an assumption. -/
def Admissible (p : Problem) (iL iR : ℂ) (f v : ℝ→ℂ) : Prop :=
  ClassicalState p.coefficient p.jumps f v ∧
  (p.left.decode ⟨f 0,v 0⟩).forward=iL ∧
  (p.right.decode ⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩).backward=iR

lemma wave_admissible (p : Problem) (iL iR : ℂ) :
    p.Admissible iL iR (p.wave iL iR) (p.waveD iL iR) := by
  refine ⟨p.classical iL iR,?_,?_⟩
  · exact congrArg Modes.forward (p.left_boundary iL iR)
  · exact congrArg Modes.backward (p.right_boundary iL iR)

/-- General finite-stack scattering uniqueness for arbitrary functions f,v;
no predetermined interior ansatz or outgoing coefficients are supplied. -/
theorem arbitrary_scattering_unique (p : Problem) (iL iR : ℂ) (f v : ℝ→ℂ)
    (h : p.Admissible iL iR f v) : f=p.wave iL iR ∧ v=p.waveD iL iR := by
  let l := p.left.decode ⟨f 0,v 0⟩
  let r := p.right.decode ⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩
  have he : p.channels.act l=r := by
    apply p.right.encode_injective
    rw [channels, channelTransfer_action]
    simp only [l, r, p.left.encode_decode, p.right.encode_decode]
    exact (p.arbitrary_endpoint h.1).symm
  have hlf : l.forward=iL := h.2.1
  have hrb : r.backward=iR := h.2.2
  have hlo : l=⟨iL,l.backward⟩ := by ext <;> simp [hlf]
  have hro : r=⟨r.forward,iR⟩ := by ext <;> simp [hrb]
  rw [hlo,hro] at he
  have hout := p.channels.outgoing_unique iL iR l.backward r.forward he
  have hlb : l.backward=(p.outgoing iL iR).1 := congrArg Prod.fst hout
  have hinit : (⟨f 0,v 0⟩ : State)=p.initial iL iR := by
    have hlall : l=⟨iL,(p.outgoing iL iR).1⟩ := by ext <;> simp [hlf,hlb]
    have enc := congrArg p.left.encode hlall
    simpa [l,initial] using enc
  constructor <;> funext x
  · have H := p.arbitrary_state_representation h.1 x
    rw [hinit] at H
    exact congrArg State.value H
  · have H := p.arbitrary_state_representation h.1 x
    rw [hinit] at H
    exact congrArg State.slope H

theorem existsUnique_classical_scattering (p : Problem) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), p.Admissible iL iR fv.1 fv.2 := by
  refine ⟨(p.wave iL iR,p.waveD iL iR),p.wave_admissible iL iR,?_⟩
  intro fv h
  obtain ⟨hf,hv⟩ := p.arbitrary_scattering_unique iL iR fv.1 fv.2 h
  exact Prod.ext hf hv

end Problem
end QuantumScattering

end Bundle_StackUniqueness

/- MODULE ExteriorModes -/
/- F1 candidate. The normalized boundary channels are proven to be the actual
traveling waves on the whole free exterior, not merely boundary labels. -/

noncomputable section Bundle_ExteriorModes
namespace QuantumScattering

def plane (k x : ℝ) : ℂ := ⟨Real.cos (k*x),Real.sin (k*x)⟩

lemma plane_neg (k x : ℝ) : plane (-k) x=star (plane k x) := by
  apply Complex.ext <;> simp [plane,neg_mul]

namespace Port
lemma root_factor (p : Port) : (p.root : ℂ)/(p.k : ℂ)=1/(p.root : ℂ) := by
  have hk : (p.k : ℂ)≠0 := by exact_mod_cast ne_of_gt p.positive
  have hr : (p.root : ℂ)≠0 := by exact_mod_cast ne_of_gt p.root_pos
  apply (div_eq_div_iff hk hr).2
  have hsq : (p.root : ℂ)^2=(p.k : ℂ) := by exact_mod_cast p.root_sq
  simpa [pow_two] using hsq

/-- Explicit plane waves with the 1/sqrt(k) factor required for unit flux. -/
theorem free_mode_value (p : Port) (z : Modes) (x : ℝ) :
    (p.profile.flow (p.encode z) x).value=
      (z.forward*plane p.k x+z.backward*plane (-p.k) x)/(p.root : ℂ) := by
  change (p.profile.C x : ℂ)*(p.encode z).value+
    (p.profile.S x : ℂ)*(p.encode z).slope=_
  rw [p.encode_value,p.encode_slope]
  dsimp [profile,LocalProfile.oscillatory]
  simp only [Complex.ofReal_div]
  calc
    _ = (Real.cos (p.k*x) : ℂ)*(z.forward+z.backward)/(p.root : ℂ)+
      (Real.sin (p.k*x) : ℂ)*((p.root : ℂ)/(p.k : ℂ))*Complex.I*(z.forward-z.backward) := by ring
    _ = _ := by
      rw [p.root_factor]
      simp only [plane, neg_mul, Real.cos_neg, Real.sin_neg,
        Complex.mk_eq_add_mul_I, Complex.ofReal_neg]
      ring
end Port

namespace Problem

theorem left_plane_wave (p : Problem) (iL iR : ℂ) (x : ℝ) (hx : x<0) :
    p.wave iL iR x=
      (iL*plane p.left.k x+(p.outgoing iL iR).1*plane (-p.left.k) x)/(p.left.root : ℂ) := by
  have he := congrArg State.value (p.left_exterior iL iR x hx)
  simpa only [wave,initial,p.left.free_mode_value] using he

theorem right_plane_wave (p : Problem) (iL iR : ℂ) (x : ℝ)
    (hx : Stack.width p.layers ≤ x) :
    p.wave iL iR x=
      ((p.outgoing iL iR).2*plane p.right.k (x-Stack.width p.layers)+
        iR*plane (-p.right.k) (x-Stack.width p.layers))/(p.right.root : ℂ) := by
  have he := congrArg State.value (p.right_exterior iL iR x hx)
  simpa only [wave,p.right.free_mode_value] using he

end Problem
end QuantumScattering

end Bundle_ExteriorModes

/- MODULE EvolutionInterface -/
/- F1 candidate. Backend interface for spatially varying REAL coefficients.
This does not assert existence for every potential. A backend must supply two
ACTUAL normalized Cauchy solutions and their derivative proofs. Unit determinant,
flux conservation and channel unitarity are derived below, never input fields. -/

noncomputable section Bundle_EvolutionInterface
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

end Bundle_EvolutionInterface

/- MODULE Framework -/
/- F1 candidate: stable public framework endpoint. Arbitrary finite geometry,
not an abstract S-matrix assumed to be physical. Not kernel-verified yet. -/

noncomputable section Bundle_Framework
namespace QuantumScattering

/-- Output contract, all fields are concluded from the physical input.
No solution, transfer matrix, current balance or S matrix is supplied by users. -/
structure FiniteScatteringCertificate (p : PhysicalProblem) : Prop where
  existence_uniqueness : ∀ iL iR : ℂ,
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), p.problem.Admissible iL iR fv.1 fv.2
  regularity : ∀ iL iR : ℂ, ContDiff ℝ 1 (p.problem.wave iL iR)
  physical_equation : ∀ (iL iR : ℂ) (x : ℝ), x∉p.problem.jumps →
    -(p.hbar^2/(2*p.mass) : ℝ) • deriv (deriv (p.problem.wave iL iR)) x +
      p.potential x • p.problem.wave iL iR x=p.energy • p.problem.wave iL iR x
  actual_flux : ∀ (iL iR : ℂ) (x : ℝ),
    current p.hbar p.mass (p.problem.wave iL iR) x=
      (p.hbar/p.mass)*(absSq iL-absSq (p.problem.outgoing iL iR).1)
  unitary_left : p.problem.channels.scatteringMatrix.conjTranspose*
    p.problem.channels.scatteringMatrix=1
  unitary_right : p.problem.channels.scatteringMatrix*
    p.problem.channels.scatteringMatrix.conjTranspose=1
  reciprocal : p.problem.channels.scatteringMatrix.transpose=p.problem.channels.scatteringMatrix
  left_modes : ∀ (iL iR : ℂ) (x : ℝ), x<0 →
    p.problem.wave iL iR x=
      (iL*plane p.problem.left.k x+
        (p.problem.outgoing iL iR).1*plane (-p.problem.left.k) x)/(p.problem.left.root : ℂ)
  right_modes : ∀ (iL iR : ℂ) (x : ℝ), Stack.width p.problem.layers ≤ x →
    p.problem.wave iL iR x=
      ((p.problem.outgoing iL iR).2*plane p.problem.right.k (x-Stack.width p.problem.layers)+
        iR*plane (-p.problem.right.k) (x-Stack.width p.problem.layers))/(p.problem.right.root : ℂ)
  positive_transmission : 0<p.problem.channels.transmission
  transparent_iff : p.problem.channels.transmission=1 ↔ p.problem.channels.beta=0

/-- Constructive reusable endpoint, quantified over any finite list of layers. -/
theorem finite_piecewise_real_scattering (p : PhysicalProblem) : FiniteScatteringCertificate p where
  existence_uniqueness := p.problem.existsUnique_classical_scattering
  regularity := p.problem.C1
  physical_equation := p.schrodinger
  actual_flux := fun iL iR x => p.problem.current_left iL iR p.hbar p.mass x
  unitary_left := p.problem.channels.unitary_matrix.1
  unitary_right := p.problem.channels.unitary_matrix.2
  reciprocal := p.problem.channels.symmetric_matrix
  left_modes := p.problem.left_plane_wave
  right_modes := p.problem.right_plane_wave
  positive_transmission := p.problem.channels.transmission_positive
  transparent_iff := p.problem.channels.transparent_iff

/-- The number of layers is not a fixed constant or an external numerical bound. -/
theorem any_finite_real_layers
    (hbar mass energy vLeft vRight : ℝ) (layers : List PhysicalLayer)
    (hh : 0<hbar) (hm : 0<mass) (hl : vLeft<energy) (hr : vRight<energy) :
    FiniteScatteringCertificate
      ⟨hbar,mass,energy,vLeft,vRight,layers,hh,hm,hl,hr⟩ :=
  finite_piecewise_real_scattering _

end QuantumScattering

end Bundle_Framework

/- MODULE TransferComposition -/
/-
F2: coherent composition of physical scattering blocks.
Proof candidates only: no Lean execution is available in the authoring runtime.
- spatial order: first M, then N;
- shared middle port: one common flux normalization and phase origin;
- denominators are proved nonzero, not assumed.
-/

noncomputable section Bundle_TransferComposition
namespace QuantumScattering
namespace ChannelTransfer

@[ext] lemma ext_coeff {M N : ChannelTransfer}
    (ha : M.alpha=N.alpha) (hb : M.beta=N.beta) : M=N := by
  cases M
  cases N
  simp_all

/-- Channel transfer through M first, then N. -/
def after (N M : ChannelTransfer) : ChannelTransfer where
  alpha := N.alpha*M.alpha + N.beta*star M.beta
  beta := N.alpha*M.beta + N.beta*star M.alpha
  balance := by
    calc
      _ = (absSq N.alpha-absSq N.beta)*(absSq M.alpha-absSq M.beta) := by
        simp [absSq,Complex.mul_re,Complex.mul_im] <;> ring
      _ = 1 := by rw [N.balance,M.balance]; norm_num

lemma after_act (N M : ChannelTransfer) (x : Modes) :
    (N.after M).act x=N.act (M.act x) := by
  ext <;> simp [after,act,star_add,star_mul,star_star] <;> ring

lemma after_assoc (K N M : ChannelTransfer) :
    K.after (N.after M)=(K.after N).after M := by
  apply ext_coeff <;> simp [after,star_add,star_mul,star_star] <;> ring

/-- Multiple internal reflections enter through a complex denominator. -/
def feedback (M N : ChannelTransfer) : ℂ := 1-M.rRight*N.rLeft

lemma feedback_factor (M N : ChannelTransfer) :
    M.feedback N=star (N.after M).alpha/(star N.alpha*star M.alpha) := by
  simp only [feedback,rRight,rLeft,after,star_add,star_mul,star_star]
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  field_simp [hm, hn] <;> ring

/-- No singular real-energy feedback denominator occurs for two open leads. -/
theorem feedback_ne_zero (M N : ChannelTransfer) : M.feedback N ≠ 0 := by
  rw [feedback_factor]
  exact div_ne_zero (N.after M).star_alpha_ne_zero
    (mul_ne_zero N.star_alpha_ne_zero M.star_alpha_ne_zero)

/-- Coherent transmission, not multiplication of transmission probabilities. -/
theorem cascade_transmission (M N : ChannelTransfer) :
    (N.after M).t=N.t*M.t/M.feedback N := by
  rw [feedback_factor]
  simp only [t]
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  have hmn : (starRingEnd ℂ) (N.after M).alpha ≠ 0 := (N.after M).star_alpha_ne_zero
  field_simp [hm, hn, hmn] <;> ring

lemma transmission_phase_balance (M : ChannelTransfer) :
    M.t^2-M.rLeft*M.rRight=M.alpha/star M.alpha := by
  simp only [t,rLeft,rRight]
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  field_simp [hm]
  linear_combination -M.complex_balance

/-- All repeat reflections are summed with their complex phases. -/
theorem cascade_reflection_left (M N : ChannelTransfer) :
    (N.after M).rLeft=M.rLeft+M.t^2*N.rLeft/M.feedback N := by
  rw [feedback_factor]
  simp only [rLeft,t,after,star_add,star_mul,star_star]
  have hden : star (N.alpha*M.alpha+N.beta*star M.beta) ≠ 0 :=
    (N.after M).star_alpha_ne_zero
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  simp only [star_add, star_mul, star_star] at hden
  have hden' : star N.alpha * star M.alpha + star N.beta * M.beta ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hm, hn, hden, hden']
  linear_combination -(star N.beta)*M.complex_balance

lemma star_complex_balance (M : ChannelTransfer) :
    star M.alpha*M.alpha-star M.beta*M.beta=1 := by
  simpa only [mul_comm] using M.complex_balance

theorem cascade_reflection_right (M N : ChannelTransfer) :
    (N.after M).rRight=N.rRight+N.t^2*M.rRight/M.feedback N := by
  rw [feedback_factor]
  simp only [rRight,t,after,star_add,star_mul,star_star]
  have hden : star (N.alpha*M.alpha+N.beta*star M.beta) ≠ 0 :=
    (N.after M).star_alpha_ne_zero
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  simp only [star_add, star_mul, star_star] at hden
  have hden' : star N.alpha * star M.alpha + star N.beta * M.beta ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hm, hn, hden, hden']
  linear_combination M.beta*N.complex_balance

lemma ext_of_action {M N : ChannelTransfer} (h : ∀ x, M.act x=N.act x) : M=N := by
  apply ext_coeff
  · simpa [act] using congrArg Modes.forward (h ⟨1,0⟩)
  · simpa [act] using congrArg Modes.forward (h ⟨0,1⟩)
end ChannelTransfer

/-- Composition in the channel basis is identical to composition of physical
state transfers; the middle port normalization cancels exactly. -/
theorem channelTransfer_after (l m r : Port) (P Q : RealTransfer) :
    channelTransfer l r (Q.after P)=
      (channelTransfer m r Q).after (channelTransfer l m P) := by
  apply ChannelTransfer.ext_of_action
  intro x
  apply r.encode_injective
  rw [ChannelTransfer.after_act,channelTransfer_action,channelTransfer_action,
    channelTransfer_action,RealTransfer.after_act]

/-- Append arbitrary finite stacks and inherit the coherent cascade law. -/
theorem stack_cascade (l m r : Port) (xs ys : Stack) :
    channelTransfer l r (Stack.transfer (xs++ys))=
      (channelTransfer m r (Stack.transfer ys)).after
        (channelTransfer l m (Stack.transfer xs)) := by
  rw [Stack.transfer_append,channelTransfer_after]

end QuantumScattering

end Bundle_TransferComposition

/- MODULE FlowComposition -/
/- F2: constant-medium propagation forms a spatial one-parameter group.
The addition law is derived from actual ODE uniqueness, not postulated.
All source in this file is an uncompiled proof candidate. -/

noncomputable section Bundle_FlowComposition
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

end Bundle_FlowComposition

/- MODULE Refinement -/
/- F2: inserting an artificial interface inside a constant medium does not
change physical scattering. This is exact refinement, NOT convergence of
piecewise approximations to an arbitrary potential. Uncompiled candidates. -/

noncomputable section Bundle_Refinement
namespace QuantumScattering
namespace Layer

def segment (δ a : ℝ) (ha : 0<a) : Layer := ⟨δ,a,ha⟩

lemma split_transfer (δ a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (segment δ (a+b) (add_pos ha hb)).transfer=
      (segment δ b hb).transfer.after (segment δ a ha).transfer := by
  exact (LocalProfile.ofDelta δ).transfer_add a b
end Layer
namespace Stack

lemma split_transfer (pre post : Stack) (δ a b : ℝ) (ha : 0<a) (hb : 0<b) :
    transfer (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post)=
      transfer (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post) := by
  simp only [transfer_append,transfer,RealTransfer.identity_after]
  rw [Layer.split_transfer]

lemma split_width (pre post : Stack) (δ a b : ℝ) (ha : 0<a) (hb : 0<b) :
    width (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post)=
      width (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post) := by
  simp [width_append,width,Layer.segment,add_assoc]

/-- All exterior amplitudes, including phases, are unchanged by subdivision. -/
theorem split_scattering (l r : Port) (pre post : Stack) (δ a b : ℝ)
    (ha : 0<a) (hb : 0<b) :
    (channelTransfer l r
      (transfer (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post))).scatteringMatrix=
    (channelTransfer l r
      (transfer (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post))).scatteringMatrix := by
  rw [split_transfer]

/-- The actual interior and exterior state agrees too, for a split first layer. -/
lemma split_tail (r : Port) (post : Stack) (δ a b : ℝ)
    (ha : 0<a) (hb : 0<b) (y : State) (x : ℝ) :
    tail r (Layer.segment δ (a+b) (add_pos ha hb)::post) y x=
      tail r (Layer.segment δ a ha::Layer.segment δ b hb::post) y x := by
  let P := LocalProfile.ofDelta δ
  have htransfer := Layer.split_transfer δ a b ha hb
  by_cases hxa : x<a
  · have hxab : x<a+b := by linarith
    simp [tail,Layer.segment,hxa,hxab,Layer.flow,Layer.profile]
  · by_cases hxab : x<a+b
    · have hxmb : x-a<b := by linarith
      simp [tail, Layer.segment, hxa, hxab, hxmb]
      change P.flow y x=P.flow (P.flow y a) (x-a)
      simpa using P.flow_add y a (x-a)
    · have hxmb : ¬x-a<b := by linarith
      simp [tail, Layer.segment, hxa, hxab, hxmb]
      have hT : (P.transfer (a+b)).act y=(P.transfer b).act ((P.transfer a).act y) := by
        rw [P.transfer_add,RealTransfer.after_act]
      change tail r post ((P.transfer (a+b)).act y) (x-(a+b))=
        tail r post ((P.transfer b).act ((P.transfer a).act y)) (x-a-b)
      rw [hT]
      congr 1
      ring

lemma split_tail_anywhere (r : Port) (pre post : Stack) (δ a b : ℝ)
    (ha : 0<a) (hb : 0<b) (y : State) (x : ℝ) :
    tail r (pre++Layer.segment δ (a+b) (add_pos ha hb)::post) y x=
      tail r (pre++Layer.segment δ a ha::Layer.segment δ b hb::post) y x := by
  induction pre generalizing y x with
  | nil => exact split_tail r post δ a b ha hb y x
  | cons s rest ih =>
    by_cases hx : x<s.width
    · simp [tail,hx]
    · simp only [List.cons_append,tail,if_neg hx]
      exact ih (s.transfer.act y) (x-s.width)

end Stack
end QuantumScattering

end Bundle_Refinement

/- MODULE Radiation -/
/- F2: only asymptotic incoming channels are prescribed; the outgoing channels
and the exterior modal representation are conclusions of the actual ODE.
The channels are flux-normalized and use each boundary as phase origin.
Uncompiled proof candidates. -/

noncomputable section Bundle_Radiation
open Filter Set
open scoped Topology
namespace QuantumScattering
namespace Port

/-- Undo free propagation back to the chosen phase origin, then decode the
state. This is the dephased, flux-normalized traveling coefficient pair. -/
def extractAt (p : Port) (o x : ℝ) (y : State) : Modes :=
  p.decode ((p.profile.transfer (x-o)).reverse.act y)

/-- Both coordinates depend on f and its ACTUAL derivative. -/
def modesAt (p : Port) (o : ℝ) (f : ℝ→ℂ) (x : ℝ) : Modes :=
  p.extractAt o x ⟨f x,deriv f x⟩

lemma extract_free (p : Port) (o x : ℝ) (y : State) :
    p.extractAt o x (p.profile.flow y (x-o))=p.decode y := by
  simp only [extractAt,LocalProfile.flow,← RealTransfer.after_act,
    RealTransfer.reverse_after,RealTransfer.identity_act]

/-- Reconstruct the actual state from extracted modes, without an ansatz. -/
lemma extract_reconstruct (p : Port) (o x : ℝ) (y : State) :
    p.profile.flow (p.encode (p.extractAt o x y)) (x-o)=y := by
  simp only [extractAt,p.encode_decode,LocalProfile.flow,← RealTransfer.after_act,
    RealTransfer.after_reverse,RealTransfer.identity_act]

lemma extract_plane_value (p : Port) (o x : ℝ) (y : State) :
    y.value=((p.extractAt o x y).forward*plane p.k (x-o)+
      (p.extractAt o x y).backward*plane (-p.k) (x-o))/(p.root:ℂ) := by
  have h := congrArg State.value (p.extract_reconstruct o x y)
  rw [p.free_mode_value] at h
  exact h.symm
end Port

namespace Problem
lemma arbitrary_left_modes (p : Problem) (f v : ℝ→ℂ)
    (h : ClassicalState p.coefficient p.jumps f v) (x : ℝ) (hx : x<0) :
    p.left.modesAt 0 f x=p.left.decode ⟨f 0,v 0⟩ := by
  have hs := p.arbitrary_state_representation h x
  rw [Stack.waveState,if_pos hx] at hs
  unfold Port.modesAt
  rw [h.deriv_eq,hs]
  simpa only [sub_zero] using p.left.extract_free 0 x ⟨f 0,v 0⟩

lemma arbitrary_right_modes (p : Problem) (f v : ℝ→ℂ)
    (h : ClassicalState p.coefficient p.jumps f v) (x : ℝ)
    (hx : Stack.width p.layers≤x) :
    p.right.modesAt (Stack.width p.layers) f x=
      p.right.decode ⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩ := by
  have h0 : 0≤x := le_trans (Stack.width_nonneg _) hx
  have hs := p.arbitrary_state_representation h x
  rw [Stack.waveState,if_neg (not_lt.mpr h0),Stack.tail_right _ _ _ _ hx] at hs
  change (⟨f x,v x⟩:State)=p.right.profile.flow
    (p.transfer.act ⟨f 0,v 0⟩) (x-Stack.width p.layers) at hs
  rw [← p.arbitrary_endpoint h] at hs
  unfold Port.modesAt
  rw [h.deriv_eq,hs]
  exact p.right.extract_free (Stack.width p.layers) x _

/-- No outgoing data, elementary span, interior basis, or current balance is
an input assumption. All discontinuities remain explicit in p.jumps. -/
def IncomingAtInfinity (p : Problem) (iL iR : ℂ) (f : ℝ→ℂ) : Prop :=
  ClassicalState p.coefficient p.jumps f (deriv f) ∧
  Tendsto (fun x => (p.left.modesAt 0 f x).forward) atBot (𝓝 iL) ∧
  Tendsto (fun x => (p.right.modesAt (Stack.width p.layers) f x).backward)
    atTop (𝓝 iR)

lemma incoming_iff_admissible (p : Problem) (iL iR : ℂ) (f : ℝ→ℂ) :
    p.IncomingAtInfinity iL iR f ↔ p.Admissible iL iR f (deriv f) := by
  constructor
  · rintro ⟨hs,hl,hr⟩
    have hleft : Tendsto (fun x=>(p.left.modesAt 0 f x).forward) atBot
        (𝓝 (p.left.decode ⟨f 0,deriv f 0⟩).forward) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
      exact (congrArg Modes.forward (p.arbitrary_left_modes f (deriv f) hs x hx)).symm
    have hright : Tendsto
        (fun x=>(p.right.modesAt (Stack.width p.layers) f x).backward) atTop
        (𝓝 (p.right.decode ⟨f (Stack.width p.layers),deriv f (Stack.width p.layers)⟩).backward) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Stack.width p.layers)] with x hx
      exact (congrArg Modes.backward (p.arbitrary_right_modes f (deriv f) hs x hx)).symm
    exact ⟨hs,tendsto_nhds_unique hleft hl,tendsto_nhds_unique hright hr⟩
  · rintro ⟨hs,hl,hr⟩
    refine ⟨hs,?_,?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
      rw [p.arbitrary_left_modes f (deriv f) hs x hx,hl]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Stack.width p.layers)] with x hx
      rw [p.arbitrary_right_modes f (deriv f) hs x hx,hr]

lemma wave_incoming (p : Problem) (iL iR : ℂ) :
    p.IncomingAtInfinity iL iR (p.wave iL iR) := by
  apply (p.incoming_iff_admissible iL iR _).mpr
  rw [(p.classical iL iR).deriv_eq]
  exact p.wave_admissible iL iR

/-- A unique actual wave for prescribed incoming limits at both infinities. -/
theorem existsUnique_incoming_at_infinity (p : Problem) (iL iR : ℂ) :
    ∃! f : ℝ→ℂ, p.IncomingAtInfinity iL iR f := by
  refine ⟨p.wave iL iR,p.wave_incoming iL iR,?_⟩
  intro f hf
  exact (p.arbitrary_scattering_unique iL iR f (deriv f)
    ((p.incoming_iff_admissible iL iR f).mp hf)).1

/-- General finite-layer current conservation applies to arbitrary classical
solutions, not just to a preselected constructed wave. -/
theorem current_arbitrary_classical (p : Problem) (f v : ℝ→ℂ)
    (h : ClassicalState p.coefficient p.jumps f v) (hbar mass x : ℝ) :
    current hbar mass f x=(hbar/mass)*(⟨f 0,v 0⟩:State).flux := by
  unfold current
  rw [h.deriv_eq]
  have hs := p.arbitrary_state_representation h x
  have hflux := congrArg State.flux hs
  rw [Stack.wave_flux] at hflux
  exact congrArg (fun u => (hbar/mass)*u) hflux
end Problem
end QuantumScattering

end Bundle_Radiation

/- MODULE EvolutionUniqueness -/
/- F2: completeness and uniqueness for a verified variable-coefficient backend.
The coefficient need not be piecewise constant. Actual fundamental solutions
and their derivatives are the backend's contract, not scattering conclusions.
Uncompiled proof candidates. -/

noncomputable section Bundle_EvolutionUniqueness
open Set
namespace QuantumScattering
namespace RealEvolution

@[simp] lemma transfer_zero (e : RealEvolution) : e.transfer 0=RealTransfer.identity := by
  ext <;> simp [transfer,RealTransfer.identity,e.a_zero,e.b_zero,e.c_zero,e.d_zero]
@[simp] lemma flow_zero (e : RealEvolution) (y : State) : e.flow y 0=y := by simp [flow]

lemma continuous_a (e : RealEvolution) : Continuous e.a :=
  (show Differentiable ℝ e.a from fun x=>(e.a_deriv x).differentiableAt).continuous
lemma continuous_b (e : RealEvolution) : Continuous e.b :=
  (show Differentiable ℝ e.b from fun x=>(e.b_deriv x).differentiableAt).continuous
lemma continuous_c (e : RealEvolution) : Continuous e.c :=
  (show Differentiable ℝ e.c from fun x=>(e.c_deriv x).differentiableAt).continuous
lemma continuous_d (e : RealEvolution) : Continuous e.d :=
  (show Differentiable ℝ e.d from fun x=>(e.d_deriv x).differentiableAt).continuous
lemma continuous_value (e : RealEvolution) (y : State) :
    Continuous (fun x=>(e.flow y x).value) :=
  (show Differentiable ℝ (fun x=>(e.flow y x).value) from
    fun x=>(e.hasDerivAt_value y x).differentiableAt).continuous
lemma continuous_slope (e : RealEvolution) (y : State) :
    Continuous (fun x=>(e.flow y x).slope) :=
  (show Differentiable ℝ (fun x=>(e.flow y x).slope) from
    fun x=>(e.hasDerivAt_slope y x).differentiableAt).continuous

def firstCoefficient (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ) : ℂ :=
  (e.d x:ℂ)*f x-(e.b x:ℂ)*v x

def secondCoefficient (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ) : ℂ :=
  -(e.c x:ℂ)*f x+(e.a x:ℂ)*v x

lemma coefficient_derivatives_zero (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ)
    (hf : HasDerivAt f (v x) x)
    (hv : HasDerivAt v (-(e.coefficient x:ℂ)*f x) x) :
    HasDerivAt (e.firstCoefficient f v) 0 x ∧
    HasDerivAt (e.secondCoefficient f v) 0 x := by
  constructor
  · have h := ((e.d_deriv x).ofReal_comp.mul hf).sub ((e.b_deriv x).ofReal_comp.mul hv)
    convert h using 1
    · rfl
    · simp [Complex.ofReal_mul]
      ring
  · have h := ((e.c_deriv x).ofReal_comp.neg.mul hf).add ((e.a_deriv x).ofReal_comp.mul hv)
    convert h using 1
    · rfl
    · simp [Complex.ofReal_mul]
      ring

lemma reconstruct (e : RealEvolution) (f v : ℝ→ℂ) (x : ℝ) :
    (e.transfer x).act ⟨e.firstCoefficient f v x,e.secondCoefficient f v x⟩=
      (⟨f x,v x⟩:State) := by
  have h : (e.a x:ℂ)*(e.d x:ℂ)-(e.b x:ℂ)*(e.c x:ℂ)=1 := by
    have hw : e.a x*e.d x-e.b x*e.c x=1 := e.wronskian_one x
    exact_mod_cast hw
  apply State.ext
  · dsimp [transfer,RealTransfer.act,firstCoefficient,secondCoefficient]
    linear_combination (f x)*h
  · dsimp [transfer,RealTransfer.act,firstCoefficient,secondCoefficient]
    linear_combination (v x)*h

/-- Every classical solution in the finite segment is represented by its actual
left endpoint data. No guessed wave ansatz is part of the hypotheses. -/
theorem state_representation (e : RealEvolution) {L : ℝ} (hL : 0<L)
    (f v : ℝ→ℂ) (hf : Continuous f) (hv : Continuous v)
    (hfv : ∀ x∈Ioo 0 L, HasDerivAt f (v x) x)
    (hode : ∀ x∈Ioo 0 L, HasDerivAt v (-(e.coefficient x:ℂ)*f x) x)
    (x : ℝ) (hx : x∈Icc 0 L) :
    (⟨f x,v x⟩:State)=e.flow ⟨f 0,v 0⟩ x := by
  have hc1 : Continuous (e.firstCoefficient f v) :=
    ((Complex.continuous_ofReal.comp e.continuous_d).mul hf).sub
      ((Complex.continuous_ofReal.comp e.continuous_b).mul hv)
  have hc2 : Continuous (e.secondCoefficient f v) :=
    ((Complex.continuous_ofReal.comp e.continuous_c).neg.mul hf).add
      ((Complex.continuous_ofReal.comp e.continuous_a).mul hv)
  have h1 := constant_on_Icc_of_deriv_zero hL hc1
    (fun y hy => (e.coefficient_derivatives_zero f v y (hfv y hy) (hode y hy)).1)
    hx (show (0:ℝ)∈Icc 0 L from ⟨le_rfl,le_of_lt hL⟩)
  have h2 := constant_on_Icc_of_deriv_zero hL hc2
    (fun y hy => (e.coefficient_derivatives_zero f v y (hfv y hy) (hode y hy)).2)
    hx (show (0:ℝ)∈Icc 0 L from ⟨le_rfl,le_of_lt hL⟩)
  have h10 : e.firstCoefficient f v 0=f 0 := by
    simp [firstCoefficient,e.d_zero,e.b_zero]
  have h20 : e.secondCoefficient f v 0=v 0 := by
    simp [secondCoefficient,e.c_zero,e.a_zero]
  rw [h10] at h1
  rw [h20] at h2
  simpa [flow,h1,h2] using (e.reconstruct f v x).symm

end RealEvolution
end QuantumScattering

end Bundle_EvolutionUniqueness

/- MODULE EvolutionSegment -/
/- F2: attach two free leads to a finite, genuinely variable-coefficient solver.
Global C1, actual ODE, physical current and arbitrary-function uniqueness use
the same channel algebra as finite constant layers. Uncompiled candidates. -/

noncomputable section Bundle_EvolutionSegment
open Set Filter
open scoped Topology
namespace QuantumScattering

structure EvolutionSegment where
  evolution : RealEvolution
  width : ℝ
  width_pos : 0<width
  left : Port
  right : Port

namespace EvolutionSegment

def transfer (s : EvolutionSegment) : RealTransfer := s.evolution.transfer s.width
def channels (s : EvolutionSegment) : ChannelTransfer := channelTransfer s.left s.right s.transfer

def rightFlow (s : EvolutionSegment) (y : State) (x : ℝ) : State :=
  s.right.profile.flow (s.transfer.act y) (x-s.width)

def tail (s : EvolutionSegment) (y : State) (x : ℝ) : State :=
  if x<s.width then s.evolution.flow y x else s.rightFlow y x

def state (s : EvolutionSegment) (y : State) (x : ℝ) : State :=
  if x<0 then s.left.profile.flow y x else s.tail y x

def coefficient (s : EvolutionSegment) (x : ℝ) : ℝ :=
  if x<0 then s.left.k^2 else if x<s.width then s.evolution.coefficient x else s.right.k^2

def jumps (s : EvolutionSegment) : Set ℝ := {x | x=0 ∨ x=s.width}

@[simp] lemma tail_zero (s : EvolutionSegment) (y : State) : s.tail y 0=y := by
  simp [tail,s.width_pos]
@[simp] lemma state_zero (s : EvolutionSegment) (y : State) : s.state y 0=y := by simp [state]
@[simp] lemma state_exit (s : EvolutionSegment) (y : State) :
    s.state y s.width=s.transfer.act y := by
  simp [state,tail,rightFlow,not_lt.mpr (le_of_lt s.width_pos)]

lemma rightFlow_value_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.rightFlow y t).value) (s.rightFlow y x).slope x := by
  simpa [Function.comp_def, rightFlow] using
    (s.right.profile.hasDerivAt_value (s.transfer.act y) (x-s.width)).scomp x
      ((hasDerivAt_id x).sub_const s.width)
lemma rightFlow_slope_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.rightFlow y t).slope)
      (-((s.right.k^2 : ℝ) : ℂ)*(s.rightFlow y x).value) x := by
  simpa [Function.comp_def, rightFlow,Port.profile,LocalProfile.oscillatory] using
    (s.right.profile.hasDerivAt_slope (s.transfer.act y) (x-s.width)).scomp x
      ((hasDerivAt_id x).sub_const s.width)

lemma tail_value_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.tail y t).value) (s.tail y x).slope x := by
  have h := hasDerivAt_join s.width
    (fun t => (s.evolution.flow y t).value) (fun t => (s.evolution.flow y t).slope)
    (fun t => (s.rightFlow y t).value) (fun t => (s.rightFlow y t).slope)
    (s.evolution.hasDerivAt_value y) (s.rightFlow_value_deriv y) (by simp [rightFlow, transfer, RealEvolution.flow]) (by simp [rightFlow, transfer, RealEvolution.flow]) x
  have heq : (fun t => (s.tail y t).value) =
      join s.width (fun t => (s.evolution.flow y t).value) (fun t => (s.rightFlow y t).value) := by
    funext t
    by_cases ht : t < s.width <;> simp [tail, join, ht]
  rw [heq]
  by_cases hx : x < s.width <;> simpa [tail, join, hx] using h

lemma tail_slope_continuous (s : EvolutionSegment) (y : State) :
    Continuous (fun t => (s.tail y t).slope) := by
  have heq : (fun t => (s.tail y t).slope) =
      join s.width (fun t => (s.evolution.flow y t).slope) (fun t => (s.rightFlow y t).slope) := by
    funext t
    by_cases ht : t < s.width <;> simp [tail, join, ht]
  rw [heq]
  exact continuous_join s.width _ _ (s.evolution.continuous_slope y) ((show Differentiable ℝ (fun t => (s.rightFlow y t).slope) from
      fun t => (s.rightFlow_slope_deriv y t).differentiableAt).continuous) (by simp [rightFlow, transfer, RealEvolution.flow])

lemma state_value_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.state y t).value) (s.state y x).slope x := by
  have h := hasDerivAt_join 0
    (fun t => (s.left.profile.flow y t).value) (fun t => (s.left.profile.flow y t).slope)
    (fun t => (s.tail y t).value) (fun t => (s.tail y t).slope)
    (s.left.profile.hasDerivAt_value y) (s.tail_value_deriv y) (by simp) (by simp) x
  have heq : (fun t => (s.state y t).value) =
      join 0 (fun t => (s.left.profile.flow y t).value) (fun t => (s.tail y t).value) := by
    funext t
    by_cases ht : t < 0 <;> simp [state, join, ht]
  rw [heq]
  by_cases hx : x < 0 <;> simpa [state, join, hx] using h

lemma state_slope_continuous (s : EvolutionSegment) (y : State) :
    Continuous (fun t => (s.state y t).slope) := by
  have heq : (fun t => (s.state y t).slope) =
      join 0 (fun t => (s.left.profile.flow y t).slope) (fun t => (s.tail y t).slope) := by
    funext t
    by_cases ht : t < 0 <;> simp [state, join, ht]
  rw [heq]
  exact continuous_join 0 _ _ (s.left.profile.continuous_slope y) (s.tail_slope_continuous y) (by simp)

lemma state_slope_deriv (s : EvolutionSegment) (y : State) (x : ℝ)
    (hx : x∉s.jumps) :
    HasDerivAt (fun t=>(s.state y t).slope)
      (-(s.coefficient x:ℂ)*(s.state y x).value) x := by
  have h0 : x≠0 := fun h=>hx (Or.inl h)
  have hL : x≠s.width := fun h=>hx (Or.inr h)
  by_cases hn : x<0
  · simp only [coefficient,state,if_pos hn]
    apply (s.left.profile.hasDerivAt_slope y x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hn] with t ht
    simp [state,show t<0 from ht]
  · have hp : 0<x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm h0)
    by_cases hi : x<s.width
    · simp only [coefficient,state,tail,if_neg hn,if_pos hi]
      apply (s.evolution.hasDerivAt_slope y x).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds (show x∈Ioo 0 s.width from ⟨hp,hi⟩)] with t ht
      simp [state,tail,not_lt.mpr (le_of_lt ht.1),ht.2]
    · have hg : s.width<x := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hL)
      simp only [coefficient,state,tail,if_neg hn,if_neg hi]
      apply (s.rightFlow_slope_deriv y x).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hg] with t ht
      change s.width < t at ht
      have ht0 : 0<t := lt_trans s.width_pos ht
      simp [state,tail,not_lt.mpr (le_of_lt ht0),not_lt.mpr (le_of_lt ht)]

lemma classical (s : EvolutionSegment) (y : State) :
    ClassicalState s.coefficient s.jumps (fun x=>(s.state y x).value)
      (fun x=>(s.state y x).slope) :=
  ⟨s.state_value_deriv y,s.state_slope_continuous y,s.state_slope_deriv y⟩

lemma state_flux (s : EvolutionSegment) (y : State) (x : ℝ) :
    (s.state y x).flux=y.flux := by
  unfold state tail rightFlow
  split_ifs
  · exact s.left.profile.flux_preserved y x
  · exact (s.evolution.transfer x).flux_preserved y
  · rw [s.right.profile.flux_preserved,s.transfer.flux_preserved]

def initial (s : EvolutionSegment) (iL iR : ℂ) : State :=
  s.left.encode ⟨iL,(s.channels.outgoing iL iR).1⟩
def wave (s : EvolutionSegment) (iL iR : ℂ) (x : ℝ) : ℂ :=
  (s.state (s.initial iL iR) x).value
def waveD (s : EvolutionSegment) (iL iR : ℂ) (x : ℝ) : ℂ :=
  (s.state (s.initial iL iR) x).slope

lemma exit_data (s : EvolutionSegment) (iL iR : ℂ) :
    s.transfer.act (s.initial iL iR)=s.right.encode ⟨(s.channels.outgoing iL iR).2,iR⟩ := by
  have h := channelTransfer_action s.left s.right s.transfer
    ⟨iL,(s.channels.outgoing iL iR).1⟩
  change s.right.encode (s.channels.act ⟨iL,(s.channels.outgoing iL iR).1⟩)=
    s.transfer.act (s.initial iL iR) at h
  rw [s.channels.outgoing_solves] at h
  exact h.symm

def Admissible (s : EvolutionSegment) (iL iR : ℂ) (f v : ℝ→ℂ) : Prop :=
  ClassicalState s.coefficient s.jumps f v ∧
  (s.left.decode ⟨f 0,v 0⟩).forward=iL ∧
  (s.right.decode ⟨f s.width,v s.width⟩).backward=iR

lemma wave_admissible (s : EvolutionSegment) (iL iR : ℂ) :
    s.Admissible iL iR (s.wave iL iR) (s.waveD iL iR) := by
  refine ⟨s.classical (s.initial iL iR),?_,?_⟩
  · change (s.left.decode (s.state (s.initial iL iR) 0)).forward=iL
    simp [initial]
  · change (s.right.decode (s.state (s.initial iL iR) s.width)).backward=iR
    rw [state_exit,exit_data,s.right.decode_encode]

lemma arbitrary_interior (s : EvolutionSegment) (f v : ℝ→ℂ)
    (h : ClassicalState s.coefficient s.jumps f v) (x : ℝ) (hx : x∈Icc 0 s.width) :
    (⟨f x,v x⟩:State)=s.evolution.flow ⟨f 0,v 0⟩ x := by
  apply s.evolution.state_representation s.width_pos f v
    (show Differentiable ℝ f from fun t=>(h.derivative t).differentiableAt).continuous
    h.continuous_slope (fun t _=>h.derivative t) _ x hx
  intro t ht
  have hj : t∉s.jumps := by
    rintro (hz|hL)
    · linarith [ht.1]
    · linarith [ht.2]
  simpa [coefficient,not_lt.mpr (le_of_lt ht.1),ht.2] using h.equation t hj

lemma arbitrary_endpoint (s : EvolutionSegment) (f v : ℝ→ℂ)
    (h : ClassicalState s.coefficient s.jumps f v) :
    (⟨f s.width,v s.width⟩:State)=s.transfer.act ⟨f 0,v 0⟩ :=
  s.arbitrary_interior f v h s.width ⟨le_of_lt s.width_pos,le_rfl⟩

lemma arbitrary_state (s : EvolutionSegment) (f v : ℝ→ℂ)
    (h : ClassicalState s.coefficient s.jumps f v) (x : ℝ) :
    (⟨f x,v x⟩:State)=s.state ⟨f 0,v 0⟩ x := by
  have hf : Continuous f :=
    (show Differentiable ℝ f from fun t=>(h.derivative t).differentiableAt).continuous
  by_cases hn : x<0
  · rw [state,if_pos hn]
    obtain ⟨h1,h2⟩ := s.left.profile.representation_on_closed_interval
      (l:=x-1) (r:=0) (o:=0) (by linarith) ⟨by linarith,le_rfl⟩
      f v hf h.continuous_slope (fun t _=>h.derivative t)
      (by
        intro t ht
        have hj : t∉s.jumps := by rintro (he|he) <;> linarith [ht.2,s.width_pos]
        simpa [coefficient,ht.2,Port.profile,LocalProfile.oscillatory,
          Complex.real_smul] using h.equation t hj)
      x ⟨by linarith,le_of_lt hn⟩
    apply State.ext
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,mul_comm] using h1
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,mul_comm,
        mul_left_comm,mul_assoc] using h2
  · rw [state,if_neg hn]
    by_cases hi : x<s.width
    · rw [tail,if_pos hi]
      exact s.arbitrary_interior f v h x ⟨le_of_not_gt hn,le_of_lt hi⟩
    · rw [tail,if_neg hi]
      have he := s.right.profile.state_representation
        (l:=s.width) (r:=x+1) (by linarith)
        f v hf h.continuous_slope (fun t _=>h.derivative t)
        (by
          intro t ht
          have ht0 : 0<t := lt_trans s.width_pos ht.1
          have hj : t∉s.jumps := by rintro (hz|hL) <;> linarith [ht.1]
          simpa [coefficient,not_lt.mpr (le_of_lt ht0),not_lt.mpr (le_of_lt ht.1),
            Port.profile,LocalProfile.oscillatory] using h.equation t hj)
        x ⟨le_of_not_gt hi,by linarith⟩
      rw [s.arbitrary_endpoint f v h] at he
      exact he

lemma arbitrary_unique (s : EvolutionSegment) (iL iR : ℂ) (f v : ℝ→ℂ)
    (h : s.Admissible iL iR f v) : f=s.wave iL iR ∧ v=s.waveD iL iR := by
  let l := s.left.decode ⟨f 0,v 0⟩
  let r := s.right.decode ⟨f s.width,v s.width⟩
  have he : s.channels.act l=r := by
    apply s.right.encode_injective
    rw [channels, channelTransfer_action]
    simp only [l, r, s.left.encode_decode, s.right.encode_decode]
    exact (s.arbitrary_endpoint f v h.1).symm
  have hl : l.forward=iL := h.2.1
  have hr : r.backward=iR := h.2.2
  have hlall : l=⟨iL,l.backward⟩ := by ext <;> simp [hl]
  have hrall : r=⟨r.forward,iR⟩ := by ext <;> simp [hr]
  rw [hlall,hrall] at he
  have hout := s.channels.outgoing_unique iL iR l.backward r.forward he
  have hbl : l.backward=(s.channels.outgoing iL iR).1 := congrArg Prod.fst hout
  have hi : (⟨f 0,v 0⟩:State)=s.initial iL iR := by
    have hh : l=⟨iL,(s.channels.outgoing iL iR).1⟩ := by ext <;> simp [hl,hbl]
    simpa [l,initial] using congrArg s.left.encode hh
  constructor <;> funext x
  · have hh := s.arbitrary_state f v h.1 x
    rw [hi] at hh
    exact congrArg State.value hh
  · have hh := s.arbitrary_state f v h.1 x
    rw [hi] at hh
    exact congrArg State.slope hh

theorem existsUnique_scattering (s : EvolutionSegment) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), s.Admissible iL iR fv.1 fv.2 := by
  refine ⟨(s.wave iL iR,s.waveD iL iR),s.wave_admissible iL iR,?_⟩
  intro fv hf
  obtain ⟨h1,h2⟩ := s.arbitrary_unique iL iR fv.1 fv.2 hf
  exact Prod.ext h1 h2

lemma current_formula (s : EvolutionSegment) (iL iR : ℂ) (hbar mass x : ℝ) :
    current hbar mass (s.wave iL iR) x=
      (hbar/mass)*(absSq iL-absSq (s.channels.outgoing iL iR).1) := by
  unfold current wave
  rw [(s.state_value_deriv (s.initial iL iR) x).deriv]
  have hh := s.state_flux (s.initial iL iR) x
  rw [initial,s.left.encode_flux] at hh
  exact congrArg (fun u=>(hbar/mass)*u) hh

/-- Shape-independent completion for any actual verified backend e. -/
theorem complete_scattering (s : EvolutionSegment) :
    (∀ iL iR, ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), s.Admissible iL iR fv.1 fv.2) ∧
    (∀ iL iR, ContDiff ℝ 1 (s.wave iL iR)) ∧
    (∀ iL iR x, x∉s.jumps → deriv (deriv (s.wave iL iR)) x=
      -(s.coefficient x:ℂ)*s.wave iL iR x) ∧
    (∀ iL iR h m x, current h m (s.wave iL iR) x=
      (h/m)*(absSq iL-absSq (s.channels.outgoing iL iR).1)) ∧
    s.channels.scatteringMatrix.conjTranspose*s.channels.scatteringMatrix=1 ∧
    s.channels.scatteringMatrix*s.channels.scatteringMatrix.conjTranspose=1 ∧
    s.channels.scatteringMatrix.transpose=s.channels.scatteringMatrix := by
  exact ⟨s.existsUnique_scattering,
    fun iL iR=>(s.classical (s.initial iL iR)).C1,
    fun iL iR x hx=>(s.classical (s.initial iL iR)).second_order x hx,
    s.current_formula,s.channels.unitary_matrix.1,s.channels.unitary_matrix.2,
    s.channels.symmetric_matrix⟩

end EvolutionSegment
end QuantumScattering

end Bundle_EvolutionSegment

/- MODULE SmoothBackend -/
/- F2: a genuinely nonconstant, explicitly soluble backend.
The normalized equation is f'' = 2/(1+x^2) * f. Its real fundamental matrix is
[[1+x^2, (x+(1+x^2) arctan x)/2], [2x, 1+x arctan x]].
No ODE solution or scattering theorem is taken as a model input.
This does NOT establish automatic existence for arbitrary continuous potentials.
Uncompiled proof candidates. -/

noncomputable section Bundle_SmoothBackend
namespace QuantumScattering
namespace SmoothBackend

lemma denominator_pos (x : ℝ) : 0<1+x^2 := by positivity
lemma denominator_ne (x : ℝ) : 1+x^2≠0 := ne_of_gt (denominator_pos x)

lemma derivative_a (x : ℝ) : HasDerivAt (fun t:ℝ=>1+t^2) (2*x) x := by
  convert ((hasDerivAt_id x).pow 2).const_add 1 using 1 <;> simp [id, Pi.mul_apply, Pi.pow_apply] <;> ring
lemma derivative_b (x : ℝ) :
    HasDerivAt (fun t:ℝ=>(t+(1+t^2)*Real.arctan t)/2)
      (1+x*Real.arctan x) x := by
  have h := ((hasDerivAt_id x).add ((derivative_a x).mul (Real.hasDerivAt_arctan x))).div_const 2
  convert h using 1
  · rfl
  · field_simp [denominator_ne x]
    ring
lemma derivative_c (x : ℝ) : HasDerivAt (fun t:ℝ=>2*t) 2 x := by
  simpa using (hasDerivAt_id x).const_mul 2
lemma derivative_d (x : ℝ) :
    HasDerivAt (fun t:ℝ=>1+t*Real.arctan t)
      (Real.arctan x+x/(1+x^2)) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).const_add 1 using 1 <;> simp [id, Pi.mul_apply, Pi.pow_apply] <;> ring

/-- Every differential certificate is discharged for the explicit functions. -/
def evolution : RealEvolution where
  coefficient := fun x=> -2/(1+x^2)
  a := fun x=>1+x^2
  b := fun x=>(x+(1+x^2)*Real.arctan x)/2
  c := fun x=>2*x
  d := fun x=>1+x*Real.arctan x
  a_zero := by norm_num
  b_zero := by norm_num
  c_zero := by norm_num
  d_zero := by norm_num
  a_deriv := derivative_a
  b_deriv := derivative_b
  c_deriv := by
    intro x
    convert derivative_c x using 1 <;> field_simp [denominator_ne x] <;> ring
  d_deriv := by
    intro x
    convert derivative_d x using 1 <;> field_simp [denominator_ne x] <;> ring

lemma coefficient_not_constant : evolution.coefficient 0≠evolution.coefficient 1 := by
  norm_num [evolution]

def segment (L : ℝ) (hL : 0<L) (l r : Port) : EvolutionSegment :=
  ⟨evolution,L,hL,l,r⟩

/-- A new, non-piecewise-constant interior solves the same global scattering
contract by calling the generic engine, with no new scattering algebra. -/
theorem smooth_scattering_unique (L : ℝ) (hL : 0<L) (l r : Port) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), (segment L hL l r).Admissible iL iR fv.1 fv.2 :=
  (segment L hL l r).existsUnique_scattering iL iR

/-- Fixing a reference energy E defines this particular physical potential.
This is an exactly soluble family at that design energy, NOT a theorem that
one fixed potential is solved at every energy by this same fundamental matrix. -/
def potential (hbar mass E : ℝ) (s : EvolutionSegment) (x : ℝ) : ℝ :=
  E-hbar^2/(2*mass)*s.coefficient x

lemma potential_inside (hbar mass E L : ℝ) (hL : 0<L) (l r : Port)
    (x : ℝ) (hx : 0<x ∧ x<L) :
    potential hbar mass E (segment L hL l r) x=E+hbar^2/(mass*(1+x^2)) := by
  simp [potential, EvolutionSegment.coefficient, segment, evolution,
    not_lt.mpr (le_of_lt hx.1), hx.2]
  simp [div_eq_mul_inv,mul_inv_rev] <;> ring

/-- Literal physical equation and C1 regularity for the global attached-lead
solution, not merely for its interior fundamental matrix. -/
theorem smooth_physical_solution (hbar mass E L : ℝ) (hh : 0<hbar) (hm : 0<mass)
    (hL : 0<L) (l r : Port) (iL iR : ℂ) :
    let s := segment L hL l r
    ContDiff ℝ 1 (s.wave iL iR) ∧
    (∀ x, x∉s.jumps →
      -(hbar^2/(2*mass):ℝ) • deriv (deriv (s.wave iL iR)) x+
        potential hbar mass E s x • s.wave iL iR x=E • s.wave iL iR x) ∧
    s.channels.scatteringMatrix.conjTranspose*s.channels.scatteringMatrix=1 := by
  dsimp only
  let s := segment L hL l r
  refine ⟨(s.classical (s.initial iL iR)).C1,?_,s.channels.unitary_matrix.1⟩
  intro x hx
  have he : deriv (deriv (s.wave iL iR)) x = -(s.coefficient x : ℂ) * s.wave iL iR x :=
    (s.classical (s.initial iL iR)).second_order x hx
  change -(hbar^2/(2*mass):ℝ) • deriv (deriv (s.wave iL iR)) x +
    potential hbar mass E s x • s.wave iL iR x = E • s.wave iL iR x
  rw [he]
  simp only [potential,Complex.real_smul]
  push_cast
  ring

end SmoothBackend
end QuantumScattering

end Bundle_SmoothBackend

/- MODULE FrameworkCompletion -/
/- F2 framework endpoints. All fields below are conclusions, not input axioms.
The single-layer legacy bridge is a separate compile target to keep the core
library independent of the old rectangular-model implementation.
Candidate source: no kernel validation is claimed in this release. -/

noncomputable section Bundle_FrameworkCompletion
namespace QuantumScattering

structure ReusableFrameworkCertificate (p : PhysicalProblem) : Prop where
  finite_layers : FiniteScatteringCertificate p
  incoming_infinity : ∀ iL iR:ℂ, ∃! f:ℝ→ℂ, p.problem.IncomingAtInfinity iL iR f
  radiation_equivalence : ∀ iL iR f,
    p.problem.IncomingAtInfinity iL iR f ↔ p.problem.Admissible iL iR f (deriv f)
  arbitrary_current : ∀ f v:ℝ→ℂ,
    ClassicalState p.problem.coefficient p.problem.jumps f v →
    ∀ x, current p.hbar p.mass f x=(p.hbar/p.mass)*(⟨f 0,v 0⟩:State).flux

theorem reusable_finite_layer_framework (p : PhysicalProblem) :
    ReusableFrameworkCertificate p where
  finite_layers := finite_piecewise_real_scattering p
  incoming_infinity := p.problem.existsUnique_incoming_at_infinity
  radiation_equivalence := p.problem.incoming_iff_admissible
  arbitrary_current := fun f v hf x =>
    p.problem.current_arbitrary_classical f v hf p.hbar p.mass x

/-- Scalar physical data and an arbitrary list remain the only model input. -/
theorem any_finite_layers_with_asymptotic_uniqueness
    (hbar mass energy vL vR : ℝ) (layers : List PhysicalLayer)
    (hh : 0<hbar) (hm : 0<mass) (hL : vL<energy) (hR : vR<energy) :
    ReusableFrameworkCertificate ⟨hbar,mass,energy,vL,vR,layers,hh,hm,hL,hR⟩ :=
  reusable_finite_layer_framework _

end QuantumScattering

end Bundle_FrameworkCompletion

#print axioms QuantumScattering.RealTransfer.flux_preserved
#print axioms QuantumScattering.RealTransfer.chain_append
#print axioms QuantumScattering.LocalProfile.local_cauchy_solution
#print axioms QuantumScattering.Stack.compositional_contract
#print axioms QuantumScattering.Port.encode_flux
#print axioms QuantumScattering.channelTransfer_action
#print axioms QuantumScattering.ChannelTransfer.existsUnique_outgoing
#print axioms QuantumScattering.ChannelTransfer.unitary_matrix
#print axioms QuantumScattering.ChannelTransfer.coherent_balance
#print axioms QuantumScattering.Stack.classical_wave
#print axioms QuantumScattering.Stack.actual_current
#print axioms QuantumScattering.LocalProfile.cauchy_unique_on_closed_interval
#print axioms QuantumScattering.Stack.tail_representation
#print axioms QuantumScattering.Problem.arbitrary_scattering_unique
#print axioms QuantumScattering.Problem.existsUnique_classical_scattering
#print axioms QuantumScattering.PhysicalProblem.schrodinger
#print axioms QuantumScattering.finite_piecewise_real_scattering
#print axioms QuantumScattering.any_finite_real_layers
#print axioms QuantumScattering.Port.free_mode_value
#print axioms QuantumScattering.Problem.left_plane_wave
#print axioms QuantumScattering.Problem.right_plane_wave
#print axioms QuantumScattering.RealEvolution.wronskian_one
#print axioms QuantumScattering.RealEvolution.actual_current
#print axioms QuantumScattering.RealEvolution.ofLocal_transfer
#print axioms QuantumScattering.RealEvolution.scattering_contract
#print axioms QuantumScattering.ChannelTransfer.feedback_ne_zero
#print axioms QuantumScattering.ChannelTransfer.cascade_transmission
#print axioms QuantumScattering.ChannelTransfer.cascade_reflection_left
#print axioms QuantumScattering.ChannelTransfer.cascade_reflection_right
#print axioms QuantumScattering.channelTransfer_after
#print axioms QuantumScattering.stack_cascade
#print axioms QuantumScattering.LocalProfile.flow_add
#print axioms QuantumScattering.LocalProfile.flow_eq_of_delta_eq
#print axioms QuantumScattering.Stack.split_scattering
#print axioms QuantumScattering.Stack.split_tail_anywhere
#print axioms QuantumScattering.Problem.incoming_iff_admissible
#print axioms QuantumScattering.Problem.existsUnique_incoming_at_infinity
#print axioms QuantumScattering.Problem.current_arbitrary_classical
#print axioms QuantumScattering.RealEvolution.state_representation
#print axioms QuantumScattering.EvolutionSegment.complete_scattering
#print axioms QuantumScattering.SmoothBackend.smooth_scattering_unique
#print axioms QuantumScattering.SmoothBackend.smooth_physical_solution
#print axioms QuantumScattering.SmoothBackend.coefficient_not_constant
#print axioms QuantumScattering.reusable_finite_layer_framework
#print axioms QuantumScattering.any_finite_layers_with_asymptotic_uniqueness
