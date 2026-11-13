/- Q4: physical perfect-transmission states and distinct positive resonant widths.
Development source; no compilation result is implied by this file. -/
import QuantumTunneling.EnergyRegimes

noncomputable section
namespace QuantumTunneling

def resonantWidth (q : ℝ) (n : ℕ) : ℝ := ((n : ℝ)+1)*Real.pi/q
lemma resonantWidth_pos (q : ℝ) (hq : 0<q) (n : ℕ) : 0<resonantWidth q n := by
  unfold resonantWidth
  exact div_pos (mul_pos (by positivity) Real.pi_pos) hq
lemma resonantWidth_phase (q : ℝ) (hq : 0<q) (n : ℕ) :
    q*resonantWidth q n=((n : ℝ)+1)*Real.pi := by
  unfold resonantWidth
  field_simp [ne_of_gt hq] <;> ring
lemma resonantWidth_strictMono (q : ℝ) (hq : 0<q) : StrictMono (resonantWidth q) := by
  intro n m hnm
  have hr : (n : ℝ)<(m : ℝ) := by exact_mod_cast hnm
  calc
    resonantWidth q n=((n : ℝ)+1)*(Real.pi/q) := by unfold resonantWidth; ring
    _<((m : ℝ)+1)*(Real.pi/q) :=
      mul_lt_mul_of_pos_right (by linarith) (div_pos Real.pi_pos hq)
    _=resonantWidth q m := by unfold resonantWidth; ring
lemma resonantWidth_injective (q : ℝ) (hq : 0<q) : Function.Injective (resonantWidth q) :=
  (resonantWidth_strictMono q hq).injective

namespace RectangularParameters

def atResonantWidth (p : RectangularParameters) (h : p.height<p.energy) (n : ℕ) :
    RectangularParameters :=
  { p with width := resonantWidth p.q n
           width_pos := resonantWidth_pos p.q (p.q_pos h) n }

theorem transmission_atResonantWidth (p : RectangularParameters) (h : p.height<p.energy)
    (n : ℕ) : (p.atResonantWidth h n).layer.T=1 := by
  apply ((p.atResonantWidth h n).above_resonance_iff h).2
  change Real.sin (p.q*resonantWidth p.q n)=0
  rw [resonantWidth_phase p.q (p.q_pos h) n]
  simpa only [Nat.cast_add,Nat.cast_one] using Real.sin_nat_mul_pi (n+1)

theorem reflection_atResonantWidth (p : RectangularParameters) (h : p.height<p.energy)
    (n : ℕ) : (p.atResonantWidth h n).layer.R=0 := by
  exact ((p.atResonantWidth h n).layer.R_eq_zero_iff).2 (p.transmission_atResonantWidth h n)

/-- Distinct indices give distinct physical barrier widths; this is not merely
reusing the same existential witness for every natural number. -/
theorem resonant_barriers_distinct (p : RectangularParameters) (h : p.height<p.energy) :
    Function.Injective (fun n => (p.atResonantWidth h n).width) :=
  resonantWidth_injective p.q (p.q_pos h)

/-- Completely transmitted physical currents, not only algebraic amplitudes. -/
theorem resonant_current_certificate (p : RectangularParameters) (h : p.height<p.energy)
    (n : ℕ) (x : ℝ) :
    current p.hbar p.mass (p.atResonantWidth h n).wave x=(p.hbar/p.mass)*p.k ∧
    current p.hbar p.mass (p.atResonantWidth h n).layer.reflectedComponent x=0 := by
  constructor
  · change current p.hbar p.mass (p.atResonantWidth h n).layer.normalizedWave x=_
    rw [ScatteringLayer.current_normalized, p.transmission_atResonantWidth h n, mul_one]
    rfl
  · rw [ScatteringLayer.current_reflectedComponent,p.reflection_atResonantWidth h n]
    ring

end RectangularParameters
end QuantumTunneling
