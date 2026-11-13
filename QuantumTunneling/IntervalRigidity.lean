/-
Q5 integration candidate, not compiled in the authoring environment.
A reusable analytic lemma: zero derivative in an open interval plus continuity
at the endpoints implies constancy on the closed interval. Endpoints are not
silently assumed twice differentiable.
-/
import QuantumTunneling.AllEnergyStatement

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumTunneling

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

/-- Continuous piecewise-constant quantities cannot change at finite interfaces. -/
lemma constant_across_two_interfaces {f : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hf : Continuous f)
    (hd : ∀ x, x ≠ 0 → x ≠ a → HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 := by
  have hmid : f a = f 0 := by
    apply constant_on_Icc_of_deriv_zero ha hf
    · intro z hz; exact hd z (ne_of_gt hz.1) (ne_of_lt hz.2)
    · exact ⟨le_of_lt ha, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt ha⟩
  by_cases hx : x ≤ 0
  · apply constant_on_Icc_of_deriv_zero (l := x-1) (r := 0) (by linarith) hf
    · intro z hz; exact hd z (ne_of_lt hz.2) (ne_of_lt (lt_trans hz.2 ha))
    · exact ⟨by linarith, hx⟩
    · exact ⟨by linarith, le_rfl⟩
  · by_cases hxa : x ≤ a
    · apply constant_on_Icc_of_deriv_zero ha hf
      · intro z hz; exact hd z (ne_of_gt hz.1) (ne_of_lt hz.2)
      · exact ⟨le_of_lt (lt_of_not_ge hx), hxa⟩
      · exact ⟨le_rfl, le_of_lt ha⟩
    · have hright : f x = f a := by
        apply constant_on_Icc_of_deriv_zero (l := a) (r := x+1) (by linarith) hf
        · intro z hz; exact hd z (ne_of_gt (lt_trans ha hz.1)) (ne_of_gt hz.1)
        · exact ⟨le_of_lt (lt_of_not_ge hxa), by linarith⟩
        · exact ⟨le_rfl, by linarith⟩
      exact hright.trans hmid

/-- Extend equality of continuous functions from an open ray to its endpoint. -/
lemma continuous_eq_at_left_endpoint {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : ℝ → F} (hf : Continuous f) (hg : Continuous g) (a : ℝ)
    (h : ∀ x, x < a → f x = g x) : f a = g a := by
  have hc : closure (Iio a) ⊆ {x | f x = g x} :=
    (isClosed_eq hf hg).closure_subset_iff.mpr h
  exact hc (by simp : a ∈ closure (Iio a))

lemma continuous_eq_at_right_endpoint {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : ℝ → F} (hf : Continuous f) (hg : Continuous g) (a : ℝ)
    (h : ∀ x, a < x → f x = g x) : f a = g a := by
  have hc : closure (Ioi a) ⊆ {x | f x = g x} :=
    (isClosed_eq hf hg).closure_subset_iff.mpr h
  exact hc (by simp : a ∈ closure (Ioi a))

end QuantumTunneling
