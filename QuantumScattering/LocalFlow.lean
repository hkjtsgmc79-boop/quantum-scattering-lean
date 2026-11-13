/- F1 candidate. Elementary local fundamental solutions extracted from Q4's
profile interface. Unlike the old physical constructor, delta can be ANY real,
so wells, barriers, free intervals and exact thresholds use the same code.
No claim of Lean verification is inherited from Q2. -/
import QuantumScattering.RealTransfer

noncomputable section
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
