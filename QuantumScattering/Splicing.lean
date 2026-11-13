/- Generic interface pasting, extracted from Q2 source and separated from the
rectangular physical model. F1 itself has not been compiled. -/
import QuantumScattering.Scattering

noncomputable section
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
