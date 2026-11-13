/- Q5: exhaustive positive integer resonance classification, in width and energy.
The word 'all' here is an iff and a unique natural-number index, not just a family
of examples. Source candidate: not kernel checked in this environment. -/
import QuantumTunneling.ThresholdContinuity

noncomputable section
namespace QuantumTunneling

lemma positive_sine_zero_iff {x:ℝ} (hx:0<x) :
    Real.sin x=0 ↔ ∃ n:ℕ, x=((n:ℝ)+1)*Real.pi := by
  constructor
  · intro hs
    obtain ⟨z,hz⟩ := Real.sin_eq_zero_iff.mp hs
    have hzreal : 0<(z:ℝ) := by
      by_contra h
      have : (z:ℝ)*Real.pi≤0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) Real.pi_nonneg
      linarith
    have hzpos : (0:ℤ)<z := by exact_mod_cast hzreal
    have hcast : (z.toNat:ℤ)=z := Int.toNat_of_nonneg (le_of_lt hzpos)
    have hnat : 0<z.toNat := by omega
    let n:=z.toNat-1
    have hn : z.toNat=n+1 := by dsimp [n]; omega
    have hzr : (z:ℝ)=(n:ℝ)+1 := by
      have hi : z=(n:ℤ)+1 := by rw [←hcast,hn]; norm_cast
      exact_mod_cast hi
    exact ⟨n,by rw [←hz,hzr]⟩
  · rintro ⟨n,rfl⟩
    simpa only [Nat.cast_add,Nat.cast_one] using Real.sin_nat_mul_pi (n+1)

lemma resonance_width_iff {q a:ℝ} (hq:0<q) (ha:0<a) :
    Real.sin (q*a)=0 ↔ ∃! n:ℕ, a=resonantWidth q n := by
  constructor
  · intro hs
    obtain ⟨n,hn⟩ := (positive_sine_zero_iff (mul_pos hq ha)).mp hs
    have hw : a=resonantWidth q n := by
      unfold resonantWidth
      apply (eq_div_iff (ne_of_gt hq)).2
      nlinarith [hn]
    refine ⟨n,hw,?_⟩
    intro j hj
    exact (resonantWidth_injective q hq) (hj.symm.trans hw)
  · rintro ⟨n,hn,_⟩
    rw [hn,resonantWidth_phase q hq n]
    simpa only [Nat.cast_add,Nat.cast_one] using Real.sin_nat_mul_pi (n+1)

namespace RectangularParameters
/-- Every positive-energy perfect-transmission state lies strictly above V0. -/
lemma perfect_transmission_above (p:RectangularParameters) (hT:p.layer.T=1) :
    p.height<p.energy := by
  rcases lt_trichotomy p.energy p.height with h|h|h
  · have ht := p.transmission_below_lt_one h; linarith
  · have ht := p.transmission_critical_lt_one h; linarith
  · exact h

/-- All, and only, the positive resonant widths; the index is unique. -/
theorem complete_resonance_classification (p:RectangularParameters) :
    p.layer.T=1 ↔ p.height<p.energy ∧ ∃! n:ℕ, p.width=resonantWidth p.q n := by
  constructor
  · intro hT
    have hE := p.perfect_transmission_above hT
    exact ⟨hE,(resonance_width_iff (p.q_pos hE) p.width_pos).mp
      ((p.above_resonance_iff hE).mp hT)⟩
  · rintro ⟨hE,hn⟩
    exact (p.above_resonance_iff hE).mpr
      ((resonance_width_iff (p.q_pos hE) p.width_pos).mpr hn)

/-- Resonant energies for a fixed physical width. -/
def resonantEnergy (p:RectangularParameters) (n:ℕ) : ℝ :=
  p.height+p.hbar^2*(((n:ℝ)+1)*Real.pi/p.width)^2/(2*p.mass)

lemma resonantEnergy_above (p:RectangularParameters) (n:ℕ) :
    p.height<p.resonantEnergy n := by
  unfold resonantEnergy
  have hk : 0<((n:ℝ)+1)*Real.pi/p.width :=
    div_pos (mul_pos (by positivity) Real.pi_pos) p.width_pos
  have h : 0<p.hbar^2*(((n:ℝ)+1)*Real.pi/p.width)^2/(2*p.mass) := by
    exact div_pos (mul_pos (pow_pos p.hbar_pos 2) (pow_pos hk 2))
      (mul_pos (by norm_num) p.mass_pos)
  linarith

lemma resonantEnergy_strictMono (p:RectangularParameters) : StrictMono p.resonantEnergy := by
  intro n m hnm
  have hnm' : (n:ℝ)<(m:ℝ) := by exact_mod_cast hnm
  have hn : 0<((n:ℝ)+1)*Real.pi/p.width :=
    div_pos (mul_pos (by positivity) Real.pi_pos) p.width_pos
  have hm : ((n:ℝ)+1)*Real.pi/p.width<((m:ℝ)+1)*Real.pi/p.width := by
    apply div_lt_div_of_pos_right _ p.width_pos
    exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  have hs : (((n:ℝ)+1)*Real.pi/p.width)^2<(((m:ℝ)+1)*Real.pi/p.width)^2 := by nlinarith
  unfold resonantEnergy
  apply add_lt_add_right
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hs (pow_pos p.hbar_pos 2))
    (mul_pos (by norm_num : (0:ℝ)<2) p.mass_pos)

lemma resonant_phase_iff_energy (p:RectangularParameters) (hE:p.height<p.energy) (n:ℕ) :
    p.q*p.width=((n:ℝ)+1)*Real.pi ↔ p.energy=p.resonantEnergy n := by
  have hq := p.q_sq hE
  have hwidth := p.width_pos
  have hmass := p.mass_pos
  have hh := p.hbar_pos
  constructor
  · intro hphase
    have hqn : p.q=((n:ℝ)+1)*Real.pi/p.width :=
      (eq_div_iff (ne_of_gt hwidth)).2 hphase
    rw [hqn] at hq
    unfold resonantEnergy
    field_simp [ne_of_gt hwidth,ne_of_gt hmass,ne_of_gt hh] at hq ⊢
    nlinarith [hq]
  · intro he
    have he' := he
    unfold resonantEnergy at he'
    have hpos : 0<((n:ℝ)+1)*Real.pi := by positivity
    have hp : 0<p.q*p.width := mul_pos (p.q_pos hE) hwidth
    have hs : (p.q*p.width)^2=(((n:ℝ)+1)*Real.pi)^2 := by
      rw [mul_pow,hq,he']
      field_simp [ne_of_gt hwidth,ne_of_gt hmass,ne_of_gt hh] <;> ring
    nlinarith

/-- An exhaustive discrete energy spectrum for perfect transmission, not a
bound-state spectral theorem. The resonant energies remain scattering energies. -/
theorem complete_resonant_energy_classification (p:RectangularParameters) :
    p.layer.T=1 ↔ ∃! n:ℕ, p.energy=p.resonantEnergy n := by
  constructor
  · intro hT
    have hE := p.perfect_transmission_above hT
    obtain ⟨n,hn⟩ := (positive_sine_zero_iff (mul_pos (p.q_pos hE) p.width_pos)).mp
      ((p.above_resonance_iff hE).mp hT)
    refine ⟨n,(p.resonant_phase_iff_energy hE n).mp hn,?_⟩
    intro j hj
    exact p.resonantEnergy_strictMono.injective
      (hj.symm.trans ((p.resonant_phase_iff_energy hE n).mp hn))
  · rintro ⟨n,hn,_⟩
    have hE : p.height<p.energy := by rw [hn]; exact p.resonantEnergy_above n
    apply (p.above_resonance_iff hE).mpr
    rw [(p.resonant_phase_iff_energy hE n).mpr hn]
    simpa only [Nat.cast_add,Nat.cast_one] using Real.sin_nat_mul_pi (n+1)
end RectangularParameters
end QuantumTunneling
