/- F1 candidate. Arbitrary-function uniqueness across any finite layer list.
No modal ansatz is an assumption on the function to be identified. -/
import QuantumScattering.LocalUniqueness
import QuantumScattering.FiniteScattering

noncomputable section
open Set
namespace QuantumScattering
namespace Stack

lemma tailJumps_positive (xs : Stack) (x : ℝ) (hx : x∈tailJumps xs) : 0<x := by
  induction xs generalizing x with
  | nil => simp [tailJumps] at hx
  | cons s rest ih =>
    simp only [tailJumps,List.mem_cons,List.mem_map] at hx
    rcases hx with h | ⟨y,hy,hxy⟩
    · simpa [h] using s.width_pos
    · rw [← hxy]
      exact add_pos s.width_pos (ih y hy)

lemma first_cell_no_jump (s : Layer) (rest : Stack) (x : ℝ) (hx : x<s.width) :
    x∉tailJumps (s::rest) := by
  intro h
  simp only [tailJumps,List.mem_cons,List.mem_map] at h
  rcases h with he | ⟨y,hy,he⟩
  · linarith
  · have hp := tailJumps_positive rest y hy
    linarith

/-- Positive half-line ODE hypotheses. They constrain only actual derivatives;
the representation in tail is a conclusion. -/
structure TailSolution (right : Port) (xs : Stack) (f v : ℝ→ℂ) : Prop where
  derivative : ∀ x, HasDerivAt f (v x) x
  continuous_slope : Continuous v
  equation : ∀ x, 0<x → x∉tailJumps xs →
    HasDerivAt v (-(tailCoefficient right xs x : ℂ)*f x) x

lemma TailSolution.continuous_value {right xs f v} (h : TailSolution right xs f v) :
    Continuous f := (show Differentiable ℝ f from fun x => (h.derivative x).differentiableAt).continuous

lemma TailSolution.first_cell {right s rest f v} (h : TailSolution right (s::rest) f v)
    (x : ℝ) (hx : x∈Icc 0 s.width) :
    (⟨f x,v x⟩ : State)=s.flow ⟨f 0,v 0⟩ x := by
  have hp := s.profile.state_representation s.width_pos f v h.continuous_value
    h.continuous_slope (fun y _ => h.derivative y)
    (by
      intro y hy
      have hd := h.equation y hy.1 (first_cell_no_jump s rest y hy.2)
      simpa [tailCoefficient,hy.2,Layer.delta_profile] using hd)
    x hx
  simpa [Layer.flow] using hp

lemma TailSolution.shift {right s rest f v} (h : TailSolution right (s::rest) f v) :
    TailSolution right rest (fun x => f (s.width+x)) (fun x => v (s.width+x)) := by
  refine ⟨?_,h.continuous_slope.comp (continuous_const.add continuous_id),?_⟩
  · intro x
    simpa [Function.comp_def] using (h.derivative (s.width+x)).scomp x ((hasDerivAt_id x).const_add s.width)
  · intro x hx hn
    have hnot : s.width+x∉tailJumps (s::rest) := by
      simp only [tailJumps,List.mem_cons,List.mem_map]
      rintro (he | ⟨y,hy,he⟩)
      · linarith
      · have hyx : y=x := by linarith
        exact hn (hyx ▸ hy)
    have hd := h.equation (s.width+x) (by linarith [s.width_pos]) hnot
    have hlt : ¬s.width+x<s.width := by linarith
    simp only [tailCoefficient,if_neg hlt] at hd
    have he : s.width+x-s.width=x := by ring
    rw [he] at hd
    simpa [Function.comp_def] using hd.scomp x ((hasDerivAt_id x).const_add s.width)

/-- Every arbitrary classical solution on the half-line equals the recursively
constructed wave for its own initial data. This is not merely coefficient uniqueness. -/
theorem tail_representation (right : Port) (xs : Stack) (f v : ℝ→ℂ)
    (h : TailSolution right xs f v) (x : ℝ) (hx : 0≤x) :
    (⟨f x,v x⟩ : State)=tail right xs ⟨f 0,v 0⟩ x := by
  induction xs generalizing f v x with
  | nil =>
    have he := right.profile.state_representation (l:=0) (r:=x+1) (by linarith)
      f v h.continuous_value h.continuous_slope (fun y _ => h.derivative y)
      (by intro y hy; exact h.equation y hy.1 (by simp [tailJumps]))
      x ⟨hx,by linarith⟩
    simpa [tail] using he
  | cons s rest ih =>
    have hend := h.first_cell s.width ⟨le_of_lt s.width_pos,le_rfl⟩
    by_cases hlt : x<s.width
    · rw [tail,if_pos hlt]
      exact h.first_cell x ⟨hx,le_of_lt hlt⟩
    · rw [tail,if_neg hlt]
      have hs := ih (fun z => f (s.width+z)) (fun z => v (s.width+z)) h.shift
        (x-s.width) (by linarith)
      have hx' : s.width+(x-s.width)=x := by ring
      simp only [hx',add_zero] at hs
      rw [hend] at hs
      exact hs

end Stack
namespace Problem

lemma arbitrary_tail {p : Problem} {f v : ℝ→ℂ}
    (h : ClassicalState p.coefficient p.jumps f v) :
    Stack.TailSolution p.right p.layers f v := by
  refine ⟨h.derivative,h.continuous_slope,?_⟩
  intro x hx hn
  have hj : x∉p.jumps := by
    intro hm
    rcases hm with he | he
    · linarith
    · exact hn he
  have hd := h.equation x hj
  simpa [coefficient,Stack.coefficient,not_lt.mpr (le_of_lt hx)] using hd

/-- Transfer data for an arbitrary classical solution, derived from its ODE. -/
lemma arbitrary_endpoint {p : Problem} {f v : ℝ→ℂ}
    (h : ClassicalState p.coefficient p.jumps f v) :
    (⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩ : State)=
      p.transfer.act ⟨f 0,v 0⟩ := by
  have he := Stack.tail_representation p.right p.layers f v (arbitrary_tail h)
    (Stack.width p.layers) (Stack.width_nonneg _)
  rw [Stack.tail_right _ _ _ _ le_rfl] at he
  simpa [transfer] using he

lemma arbitrary_state_representation {p : Problem} {f v : ℝ→ℂ}
    (h : ClassicalState p.coefficient p.jumps f v) (x : ℝ) :
    (⟨f x,v x⟩ : State)=Stack.waveState p.left p.right p.layers ⟨f 0,v 0⟩ x := by
  by_cases hn : x<0
  · rw [Stack.waveState,if_pos hn]
    have hf : Continuous f :=
      (show Differentiable ℝ f from fun y => (h.derivative y).differentiableAt).continuous
    obtain ⟨hv,hd⟩ := p.left.profile.representation_on_closed_interval
      (l:=x-1) (r:=0) (o:=0) (by linarith) ⟨by linarith,le_rfl⟩
      f v hf h.continuous_slope (fun y _ => h.derivative y)
      (by
        intro y hy
        have hj : y∉p.jumps := by
          intro he
          rcases he with he | he
          · exact (ne_of_lt hy.2) he
          · exact (not_lt_of_gt hy.2) (Stack.tailJumps_positive p.layers y he)
        have H := h.equation y hj
        simpa [coefficient,Stack.coefficient,hy.2,Port.profile,
          LocalProfile.oscillatory,Complex.real_smul] using H)
      x ⟨by linarith,le_of_lt hn⟩
    apply State.ext
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,mul_comm] using hv
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,
        Complex.real_smul,mul_comm,mul_left_comm,mul_assoc] using hd
  · rw [Stack.waveState,if_neg hn]
    exact Stack.tail_representation p.right p.layers f v (arbitrary_tail h) x (le_of_not_gt hn)

/-- Exact incoming channel data at the interfaces. Because the exterior ODE is
free, these are the traveling-wave coefficients throughout the exterior rays.
An asymptotic-limit formulation is deliberately a separate API, not an assumption. -/
def Admissible (p : Problem) (iL iR : ℂ) (f v : ℝ→ℂ) : Prop :=
  ClassicalState p.coefficient p.jumps f v ∧
  (p.left.decode ⟨f 0,v 0⟩).forward=iL ∧
  (p.right.decode ⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩).backward=iR

lemma wave_admissible (p : Problem) (iL iR : ℂ) :
    p.Admissible iL iR (p.wave iL iR) (p.waveD iL iR) := by
  refine ⟨p.classical iL iR,?_,?_⟩
  · exact congrArg Modes.forward (p.left_boundary iL iR)
  · exact congrArg Modes.backward (p.right_boundary iL iR)

/-- General finite-stack scattering uniqueness for arbitrary functions f,v;
no predetermined interior ansatz or outgoing coefficients are supplied. -/
theorem arbitrary_scattering_unique (p : Problem) (iL iR : ℂ) (f v : ℝ→ℂ)
    (h : p.Admissible iL iR f v) : f=p.wave iL iR ∧ v=p.waveD iL iR := by
  let l := p.left.decode ⟨f 0,v 0⟩
  let r := p.right.decode ⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩
  have he : p.channels.act l=r := by
    apply p.right.encode_injective
    rw [channels, channelTransfer_action]
    simp only [l, r, p.left.encode_decode, p.right.encode_decode]
    exact (p.arbitrary_endpoint h.1).symm
  have hlf : l.forward=iL := h.2.1
  have hrb : r.backward=iR := h.2.2
  have hlo : l=⟨iL,l.backward⟩ := by ext <;> simp [hlf]
  have hro : r=⟨r.forward,iR⟩ := by ext <;> simp [hrb]
  rw [hlo,hro] at he
  have hout := p.channels.outgoing_unique iL iR l.backward r.forward he
  have hlb : l.backward=(p.outgoing iL iR).1 := congrArg Prod.fst hout
  have hinit : (⟨f 0,v 0⟩ : State)=p.initial iL iR := by
    have hlall : l=⟨iL,(p.outgoing iL iR).1⟩ := by ext <;> simp [hlf,hlb]
    have enc := congrArg p.left.encode hlall
    simpa [l,initial] using enc
  constructor <;> funext x
  · have H := p.arbitrary_state_representation h.1 x
    rw [hinit] at H
    exact congrArg State.value H
  · have H := p.arbitrary_state_representation h.1 x
    rw [hinit] at H
    exact congrArg State.slope H

theorem existsUnique_classical_scattering (p : Problem) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), p.Admissible iL iR fv.1 fv.2 := by
  refine ⟨(p.wave iL iR,p.waveD iL iR),p.wave_admissible iL iR,?_⟩
  intro fv h
  obtain ⟨hf,hv⟩ := p.arbitrary_scattering_unique iL iR fv.1 fv.2 h
  exact Prod.ext hf hv

end Problem
end QuantumScattering
