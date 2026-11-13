/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

Q2: checked with Lean 4.30.0; the complete build evidence is recorded in reports.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext

/-!
# Finite rectangular barrier, below-barrier regime
Only positive physical input data are assumed. No solution, matching condition,
probability formula, or conservation law is an input field.

We use stationary scattering states, not normalized L² eigenvectors. Potential
values at the two interfaces do not enter the pointwise differential equation.
-/
noncomputable section
namespace QuantumTunneling

structure Parameters where
  hbar : ℝ
  mass : ℝ
  energy : ℝ
  height : ℝ
  width : ℝ
  hbar_pos : 0 < hbar
  mass_pos : 0 < mass
  energy_pos : 0 < energy
  below_barrier : energy < height
  width_pos : 0 < width

/-- An intermediate parameterization. It is later constructed from physical data. -/
structure Spectral where
  k : ℝ
  κ : ℝ
  a : ℝ
  k_pos : 0 < k
  κ_pos : 0 < κ
  a_pos : 0 < a

namespace Parameters

def waveNumber (p : Parameters) : ℝ := Real.sqrt (2 * p.mass * p.energy) / p.hbar
def decayNumber (p : Parameters) : ℝ :=
  Real.sqrt (2 * p.mass * (p.height - p.energy)) / p.hbar

def potential (p : Parameters) (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ p.width then p.height else 0

lemma height_pos (p : Parameters) : 0 < p.height :=
  lt_trans p.energy_pos p.below_barrier
lemma gap_pos (p : Parameters) : 0 < p.height - p.energy :=
  sub_pos.mpr p.below_barrier
lemma waveNumber_pos (p : Parameters) : 0 < p.waveNumber := by
  apply div_pos _ p.hbar_pos
  apply Real.sqrt_pos.2
  exact mul_pos (mul_pos (by norm_num) p.mass_pos) p.energy_pos
lemma decayNumber_pos (p : Parameters) : 0 < p.decayNumber := by
  apply div_pos _ p.hbar_pos
  apply Real.sqrt_pos.2
  exact mul_pos (mul_pos (by norm_num) p.mass_pos) p.gap_pos

lemma waveNumber_sq (p : Parameters) :
    p.waveNumber ^ 2 = 2 * p.mass * p.energy / p.hbar ^ 2 := by
  rw [waveNumber, div_pow, Real.sq_sqrt]
  exact le_of_lt (mul_pos (mul_pos (by norm_num) p.mass_pos) p.energy_pos)
lemma decayNumber_sq (p : Parameters) :
    p.decayNumber ^ 2 = 2 * p.mass * (p.height - p.energy) / p.hbar ^ 2 := by
  rw [decayNumber, div_pow, Real.sq_sqrt]
  exact le_of_lt (mul_pos (mul_pos (by norm_num) p.mass_pos) p.gap_pos)

def spectral (p : Parameters) : Spectral :=
  ⟨p.waveNumber, p.decayNumber, p.width, p.waveNumber_pos, p.decayNumber_pos, p.width_pos⟩

lemma kinetic_waveNumber (p : Parameters) :
    p.hbar ^ 2 / (2 * p.mass) * p.waveNumber ^ 2 = p.energy := by
  rw [p.waveNumber_sq]
  field_simp [ne_of_gt p.hbar_pos, ne_of_gt p.mass_pos]
  <;> ring
lemma kinetic_decayNumber (p : Parameters) :
    p.hbar ^ 2 / (2 * p.mass) * p.decayNumber ^ 2 = p.height - p.energy := by
  rw [p.decayNumber_sq]
  field_simp [ne_of_gt p.hbar_pos, ne_of_gt p.mass_pos]
  <;> ring

end Parameters
end QuantumTunneling
