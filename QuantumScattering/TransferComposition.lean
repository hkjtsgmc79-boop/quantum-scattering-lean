/-
F2: coherent composition of physical scattering blocks.
Proof candidates only: no Lean execution is available in the authoring runtime.
- spatial order: first M, then N;
- shared middle port: one common flux normalization and phase origin;
- denominators are proved nonzero, not assumed.
-/
import QuantumScattering.Framework

noncomputable section
namespace QuantumScattering
namespace ChannelTransfer

@[ext] lemma ext_coeff {M N : ChannelTransfer}
    (ha : M.alpha=N.alpha) (hb : M.beta=N.beta) : M=N := by
  cases M
  cases N
  simp_all

/-- Channel transfer through M first, then N. -/
def after (N M : ChannelTransfer) : ChannelTransfer where
  alpha := N.alpha*M.alpha + N.beta*star M.beta
  beta := N.alpha*M.beta + N.beta*star M.alpha
  balance := by
    calc
      _ = (absSq N.alpha-absSq N.beta)*(absSq M.alpha-absSq M.beta) := by
        simp [absSq,Complex.mul_re,Complex.mul_im] <;> ring
      _ = 1 := by rw [N.balance,M.balance]; norm_num

lemma after_act (N M : ChannelTransfer) (x : Modes) :
    (N.after M).act x=N.act (M.act x) := by
  ext <;> simp [after,act,star_add,star_mul,star_star] <;> ring

lemma after_assoc (K N M : ChannelTransfer) :
    K.after (N.after M)=(K.after N).after M := by
  apply ext_coeff <;> simp [after,star_add,star_mul,star_star] <;> ring

/-- Multiple internal reflections enter through a complex denominator. -/
def feedback (M N : ChannelTransfer) : ℂ := 1-M.rRight*N.rLeft

lemma feedback_factor (M N : ChannelTransfer) :
    M.feedback N=star (N.after M).alpha/(star N.alpha*star M.alpha) := by
  simp only [feedback,rRight,rLeft,after,star_add,star_mul,star_star]
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  field_simp [hm, hn] <;> ring

/-- No singular real-energy feedback denominator occurs for two open leads. -/
theorem feedback_ne_zero (M N : ChannelTransfer) : M.feedback N ≠ 0 := by
  rw [feedback_factor]
  exact div_ne_zero (N.after M).star_alpha_ne_zero
    (mul_ne_zero N.star_alpha_ne_zero M.star_alpha_ne_zero)

/-- Coherent transmission, not multiplication of transmission probabilities. -/
theorem cascade_transmission (M N : ChannelTransfer) :
    (N.after M).t=N.t*M.t/M.feedback N := by
  rw [feedback_factor]
  simp only [t]
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  have hmn : (starRingEnd ℂ) (N.after M).alpha ≠ 0 := (N.after M).star_alpha_ne_zero
  field_simp [hm, hn, hmn] <;> ring

lemma transmission_phase_balance (M : ChannelTransfer) :
    M.t^2-M.rLeft*M.rRight=M.alpha/star M.alpha := by
  simp only [t,rLeft,rRight]
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  field_simp [hm]
  linear_combination -M.complex_balance

/-- All repeat reflections are summed with their complex phases. -/
theorem cascade_reflection_left (M N : ChannelTransfer) :
    (N.after M).rLeft=M.rLeft+M.t^2*N.rLeft/M.feedback N := by
  rw [feedback_factor]
  simp only [rLeft,t,after,star_add,star_mul,star_star]
  have hden : star (N.alpha*M.alpha+N.beta*star M.beta) ≠ 0 :=
    (N.after M).star_alpha_ne_zero
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  simp only [star_add, star_mul, star_star] at hden
  have hden' : star N.alpha * star M.alpha + star N.beta * M.beta ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hm, hn, hden, hden']
  linear_combination -(star N.beta)*M.complex_balance

lemma star_complex_balance (M : ChannelTransfer) :
    star M.alpha*M.alpha-star M.beta*M.beta=1 := by
  simpa only [mul_comm] using M.complex_balance

theorem cascade_reflection_right (M N : ChannelTransfer) :
    (N.after M).rRight=N.rRight+N.t^2*M.rRight/M.feedback N := by
  rw [feedback_factor]
  simp only [rRight,t,after,star_add,star_mul,star_star]
  have hden : star (N.alpha*M.alpha+N.beta*star M.beta) ≠ 0 :=
    (N.after M).star_alpha_ne_zero
  have hm : (starRingEnd ℂ) M.alpha ≠ 0 := M.star_alpha_ne_zero
  have hn : (starRingEnd ℂ) N.alpha ≠ 0 := N.star_alpha_ne_zero
  simp only [star_add, star_mul, star_star] at hden
  have hden' : star N.alpha * star M.alpha + star N.beta * M.beta ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hm, hn, hden, hden']
  linear_combination M.beta*N.complex_balance

lemma ext_of_action {M N : ChannelTransfer} (h : ∀ x, M.act x=N.act x) : M=N := by
  apply ext_coeff
  · simpa [act] using congrArg Modes.forward (h ⟨1,0⟩)
  · simpa [act] using congrArg Modes.forward (h ⟨0,1⟩)
end ChannelTransfer

/-- Composition in the channel basis is identical to composition of physical
state transfers; the middle port normalization cancels exactly. -/
theorem channelTransfer_after (l m r : Port) (P Q : RealTransfer) :
    channelTransfer l r (Q.after P)=
      (channelTransfer m r Q).after (channelTransfer l m P) := by
  apply ChannelTransfer.ext_of_action
  intro x
  apply r.encode_injective
  rw [ChannelTransfer.after_act,channelTransfer_action,channelTransfer_action,
    channelTransfer_action,RealTransfer.after_act]

/-- Append arbitrary finite stacks and inherit the coherent cascade law. -/
theorem stack_cascade (l m r : Port) (xs ys : Stack) :
    channelTransfer l r (Stack.transfer (xs++ys))=
      (channelTransfer m r (Stack.transfer ys)).after
        (channelTransfer l m (Stack.transfer xs)) := by
  rw [Stack.transfer_append,channelTransfer_after]

end QuantumScattering
