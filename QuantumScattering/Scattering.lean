/- F1 candidate. A general reciprocal two-port S matrix: rL and rR need NOT
be equal as complex numbers. All quantities use the boundary-phase convention
and unit-flux normalization fixed in Channels.lean. -/
import QuantumScattering.Channels

noncomputable section
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
