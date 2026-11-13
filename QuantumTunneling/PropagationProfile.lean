/-
Q4 development source. NOT compiled in this authoring environment.
A common fundamental-solution interface includes the threshold delta = 0.
All fields below are proved for explicit elementary functions before the public
physical theorem uses them; no physical solution is supplied as an input.
-/
import QuantumTunneling.C1Regularity
import QuantumTunneling.MatchingUniqueness

noncomputable section
namespace QuantumTunneling

/-- Real fundamental solutions of u'' = -delta*u with fixed initial data. -/
structure PropagationProfile where
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

namespace PropagationProfile

/-- Exact threshold: no division by a vanishing interior wave number. -/
def critical : PropagationProfile where
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
def oscillatory (q : ℝ) (hq : 0 < q) : PropagationProfile where
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
def evanescent (κ : ℝ) (hκ : 0 < κ) : PropagationProfile where
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

end PropagationProfile

/-- Auxiliary spectral data, later constructed from positive physical data. -/
structure ScatteringLayer where
  k : ℝ
  a : ℝ
  k_pos : 0 < k
  a_pos : 0 < a
  profile : PropagationProfile

end QuantumTunneling
