/- F1 candidate. The normalized boundary channels are proven to be the actual
traveling waves on the whole free exterior, not merely boundary labels. -/
import QuantumScattering.FiniteScattering

noncomputable section
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
