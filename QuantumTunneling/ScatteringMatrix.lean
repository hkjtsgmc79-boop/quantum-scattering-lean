/-
Q5: the boundary-referenced two-port S matrix. Both ports use the barrier
interfaces as phase origins. This convention is essential for exact symmetry.
Not compiled in this authoring environment.
-/
import QuantumTunneling.FundamentalRepresentation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

noncomputable section
open scoped BigOperators
namespace QuantumTunneling

lemma star_mul_self_absSq (z : ℂ) : star z*z=(absSq z : ℂ) := by
  rw [mul_comm]
  simpa [absSq, Complex.normSq_apply, pow_two] using Complex.mul_conj z

lemma mul_star_self_absSq (z : ℂ) : z*star z=(absSq z : ℂ) := by
  rw [mul_comm,star_mul_self_absSq]

lemma absSq_eq_zero_iff (z : ℂ) : absSq z=0 ↔ z=0 := by
  rw [absSq_eq_norm_sq,sq_eq_zero_iff,norm_eq_zero]

lemma absSq_add (z w : ℂ) :
    absSq (z+w)=absSq z+absSq w+(star z*w+star w*z).re := by
  simp [absSq,Complex.mul_re] <;> ring

namespace ScatteringLayer

/-- Left/right outgoing amplitudes, in that order, versus left/right incoming
amplitudes. Right plane-wave phases are measured from x=a, left from x=0. -/
def scatteringMatrix (s : ScatteringLayer) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i=j then s.reflectionAmplitude else s.transmissionAmplitude

def outgoingLeft (s : ScatteringLayer) (inL inR : ℂ) : ℂ :=
  s.reflectionAmplitude*inL+s.transmissionAmplitude*inR

def outgoingRight (s : ScatteringLayer) (inL inR : ℂ) : ℂ :=
  s.transmissionAmplitude*inL+s.reflectionAmplitude*inR

lemma B_pure_imaginary (s : ScatteringLayer) : star s.B = -s.B := by
  apply Complex.ext <;> simp [B]

lemma Astar_ne_zero (s : ScatteringLayer) : star s.A ≠ 0 := by
  intro h
  apply s.A_ne_zero
  have hh := congrArg star h
  simpa using hh

lemma diagonal_unit (s : ScatteringLayer) :
    star s.reflectionAmplitude*s.reflectionAmplitude +
      star s.transmissionAmplitude*s.transmissionAmplitude = 1 := by
  rw [star_mul_self_absSq,star_mul_self_absSq,← Complex.ofReal_add]
  exact_mod_cast s.R_add_T

/-- The extra phase relation that probability balance alone does not provide. -/
lemma off_diagonal_zero (s : ScatteringLayer) :
    star s.reflectionAmplitude*s.transmissionAmplitude +
      star s.transmissionAmplitude*s.reflectionAmplitude = 0 := by
  unfold reflectionAmplitude transmissionAmplitude
  simp only [star_div₀, star_one, s.B_pure_imaginary]
  ring

lemma scatteringMatrix_symmetric (s : ScatteringLayer) :
    s.scatteringMatrix.transpose=s.scatteringMatrix := by
  ext i j
  simp only [Matrix.transpose_apply,scatteringMatrix]
  by_cases h : i=j <;> simp [h,eq_comm]

/-- Full complex unitarity, not just R+T=1 for a single incident channel. -/
theorem scatteringMatrix_unitary (s : ScatteringLayer) :
    s.scatteringMatrix.conjTranspose*s.scatteringMatrix=1 ∧
    s.scatteringMatrix*s.scatteringMatrix.conjTranspose=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [scatteringMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two] <;>
    simp only [starRingEnd_apply] <;>
    first
    | simpa only [add_comm, mul_comm] using s.diagonal_unit
    | simpa only [add_comm, mul_comm] using s.off_diagonal_zero

lemma outgoing_eq_matrix (s : ScatteringLayer) (inL inR : ℂ) :
    s.scatteringMatrix.mulVec ![inL,inR] =
      ![s.outgoingLeft inL inR,s.outgoingRight inL inR] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,scatteringMatrix,
    Fin.sum_univ_two,outgoingLeft,outgoingRight]

/-- Norm conservation for arbitrary coherent simultaneous incidence. Interference
terms are cancelled by off_diagonal_zero, not assumed absent. -/
theorem coherent_probability_balance (s : ScatteringLayer) (inL inR : ℂ) :
    absSq (s.outgoingLeft inL inR)+absSq (s.outgoingRight inL inR)=
      absSq inL+absSq inR := by
  have hdiag := s.diagonal_unit
  have hcross := s.off_diagonal_zero
  have h := congrArg Complex.re (show
      star (s.outgoingLeft inL inR)*s.outgoingLeft inL inR+
        star (s.outgoingRight inL inR)*s.outgoingRight inL inR =
      star inL*inL+star inR*inR from by
    calc
      _ = (star s.reflectionAmplitude*s.reflectionAmplitude+
            star s.transmissionAmplitude*s.transmissionAmplitude)*
              (star inL*inL+star inR*inR)+
          (star s.reflectionAmplitude*s.transmissionAmplitude+
            star s.transmissionAmplitude*s.reflectionAmplitude)*
              (star inL*inR+star inR*inL) := by
                simp only [outgoingLeft,outgoingRight,star_add,star_mul]; ring
      _ = _ := by rw [hdiag,hcross]; ring)
  simpa only [star_mul_self_absSq,Complex.add_re,Complex.ofReal_re] using h

/-- Transfer matrix, useful independently of the S-matrix representation. -/
def transferMatrix (s : ScatteringLayer) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![s.A,-s.B; s.B,star s.A]

lemma transfer_det_one (s : ScatteringLayer) : s.transferMatrix.det=1 := by
  rw [transferMatrix,Matrix.det_fin_two]
  have h : s.A*star s.A+s.B^2=1 := by
    have hb : s.B^2=-(absSq s.B : ℂ) := by
      have hB := star_mul_self_absSq s.B
      rw [s.B_pure_imaginary] at hB
      linear_combination -hB
    rw [mul_star_self_absSq,hb]
    exact_mod_cast s.amplitude_balance
  simpa [pow_two] using h

end ScatteringLayer
end QuantumTunneling
