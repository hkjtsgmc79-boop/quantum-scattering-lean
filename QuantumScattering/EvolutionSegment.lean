/- F2: attach two free leads to a finite, genuinely variable-coefficient solver.
Global C1, actual ODE, physical current and arbitrary-function uniqueness use
the same channel algebra as finite constant layers. Uncompiled candidates. -/
import QuantumScattering.EvolutionUniqueness
import QuantumScattering.Radiation

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumScattering

structure EvolutionSegment where
  evolution : RealEvolution
  width : ℝ
  width_pos : 0<width
  left : Port
  right : Port

namespace EvolutionSegment

def transfer (s : EvolutionSegment) : RealTransfer := s.evolution.transfer s.width
def channels (s : EvolutionSegment) : ChannelTransfer := channelTransfer s.left s.right s.transfer

def rightFlow (s : EvolutionSegment) (y : State) (x : ℝ) : State :=
  s.right.profile.flow (s.transfer.act y) (x-s.width)

def tail (s : EvolutionSegment) (y : State) (x : ℝ) : State :=
  if x<s.width then s.evolution.flow y x else s.rightFlow y x

def state (s : EvolutionSegment) (y : State) (x : ℝ) : State :=
  if x<0 then s.left.profile.flow y x else s.tail y x

def coefficient (s : EvolutionSegment) (x : ℝ) : ℝ :=
  if x<0 then s.left.k^2 else if x<s.width then s.evolution.coefficient x else s.right.k^2

def jumps (s : EvolutionSegment) : Set ℝ := {x | x=0 ∨ x=s.width}

@[simp] lemma tail_zero (s : EvolutionSegment) (y : State) : s.tail y 0=y := by
  simp [tail,s.width_pos]
@[simp] lemma state_zero (s : EvolutionSegment) (y : State) : s.state y 0=y := by simp [state]
@[simp] lemma state_exit (s : EvolutionSegment) (y : State) :
    s.state y s.width=s.transfer.act y := by
  simp [state,tail,rightFlow,not_lt.mpr (le_of_lt s.width_pos)]

lemma rightFlow_value_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.rightFlow y t).value) (s.rightFlow y x).slope x := by
  simpa [Function.comp_def, rightFlow] using
    (s.right.profile.hasDerivAt_value (s.transfer.act y) (x-s.width)).scomp x
      ((hasDerivAt_id x).sub_const s.width)
lemma rightFlow_slope_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.rightFlow y t).slope)
      (-((s.right.k^2 : ℝ) : ℂ)*(s.rightFlow y x).value) x := by
  simpa [Function.comp_def, rightFlow,Port.profile,LocalProfile.oscillatory] using
    (s.right.profile.hasDerivAt_slope (s.transfer.act y) (x-s.width)).scomp x
      ((hasDerivAt_id x).sub_const s.width)

lemma tail_value_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.tail y t).value) (s.tail y x).slope x := by
  have h := hasDerivAt_join s.width
    (fun t => (s.evolution.flow y t).value) (fun t => (s.evolution.flow y t).slope)
    (fun t => (s.rightFlow y t).value) (fun t => (s.rightFlow y t).slope)
    (s.evolution.hasDerivAt_value y) (s.rightFlow_value_deriv y) (by simp [rightFlow, transfer, RealEvolution.flow]) (by simp [rightFlow, transfer, RealEvolution.flow]) x
  have heq : (fun t => (s.tail y t).value) =
      join s.width (fun t => (s.evolution.flow y t).value) (fun t => (s.rightFlow y t).value) := by
    funext t
    by_cases ht : t < s.width <;> simp [tail, join, ht]
  rw [heq]
  by_cases hx : x < s.width <;> simpa [tail, join, hx] using h

lemma tail_slope_continuous (s : EvolutionSegment) (y : State) :
    Continuous (fun t => (s.tail y t).slope) := by
  have heq : (fun t => (s.tail y t).slope) =
      join s.width (fun t => (s.evolution.flow y t).slope) (fun t => (s.rightFlow y t).slope) := by
    funext t
    by_cases ht : t < s.width <;> simp [tail, join, ht]
  rw [heq]
  exact continuous_join s.width _ _ (s.evolution.continuous_slope y) ((show Differentiable ℝ (fun t => (s.rightFlow y t).slope) from
      fun t => (s.rightFlow_slope_deriv y t).differentiableAt).continuous) (by simp [rightFlow, transfer, RealEvolution.flow])

lemma state_value_deriv (s : EvolutionSegment) (y : State) (x : ℝ) :
    HasDerivAt (fun t=>(s.state y t).value) (s.state y x).slope x := by
  have h := hasDerivAt_join 0
    (fun t => (s.left.profile.flow y t).value) (fun t => (s.left.profile.flow y t).slope)
    (fun t => (s.tail y t).value) (fun t => (s.tail y t).slope)
    (s.left.profile.hasDerivAt_value y) (s.tail_value_deriv y) (by simp) (by simp) x
  have heq : (fun t => (s.state y t).value) =
      join 0 (fun t => (s.left.profile.flow y t).value) (fun t => (s.tail y t).value) := by
    funext t
    by_cases ht : t < 0 <;> simp [state, join, ht]
  rw [heq]
  by_cases hx : x < 0 <;> simpa [state, join, hx] using h

lemma state_slope_continuous (s : EvolutionSegment) (y : State) :
    Continuous (fun t => (s.state y t).slope) := by
  have heq : (fun t => (s.state y t).slope) =
      join 0 (fun t => (s.left.profile.flow y t).slope) (fun t => (s.tail y t).slope) := by
    funext t
    by_cases ht : t < 0 <;> simp [state, join, ht]
  rw [heq]
  exact continuous_join 0 _ _ (s.left.profile.continuous_slope y) (s.tail_slope_continuous y) (by simp)

lemma state_slope_deriv (s : EvolutionSegment) (y : State) (x : ℝ)
    (hx : x∉s.jumps) :
    HasDerivAt (fun t=>(s.state y t).slope)
      (-(s.coefficient x:ℂ)*(s.state y x).value) x := by
  have h0 : x≠0 := fun h=>hx (Or.inl h)
  have hL : x≠s.width := fun h=>hx (Or.inr h)
  by_cases hn : x<0
  · simp only [coefficient,state,if_pos hn]
    apply (s.left.profile.hasDerivAt_slope y x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hn] with t ht
    simp [state,show t<0 from ht]
  · have hp : 0<x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm h0)
    by_cases hi : x<s.width
    · simp only [coefficient,state,tail,if_neg hn,if_pos hi]
      apply (s.evolution.hasDerivAt_slope y x).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds (show x∈Ioo 0 s.width from ⟨hp,hi⟩)] with t ht
      simp [state,tail,not_lt.mpr (le_of_lt ht.1),ht.2]
    · have hg : s.width<x := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hL)
      simp only [coefficient,state,tail,if_neg hn,if_neg hi]
      apply (s.rightFlow_slope_deriv y x).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hg] with t ht
      change s.width < t at ht
      have ht0 : 0<t := lt_trans s.width_pos ht
      simp [state,tail,not_lt.mpr (le_of_lt ht0),not_lt.mpr (le_of_lt ht)]

lemma classical (s : EvolutionSegment) (y : State) :
    ClassicalState s.coefficient s.jumps (fun x=>(s.state y x).value)
      (fun x=>(s.state y x).slope) :=
  ⟨s.state_value_deriv y,s.state_slope_continuous y,s.state_slope_deriv y⟩

lemma state_flux (s : EvolutionSegment) (y : State) (x : ℝ) :
    (s.state y x).flux=y.flux := by
  unfold state tail rightFlow
  split_ifs
  · exact s.left.profile.flux_preserved y x
  · exact (s.evolution.transfer x).flux_preserved y
  · rw [s.right.profile.flux_preserved,s.transfer.flux_preserved]

def initial (s : EvolutionSegment) (iL iR : ℂ) : State :=
  s.left.encode ⟨iL,(s.channels.outgoing iL iR).1⟩
def wave (s : EvolutionSegment) (iL iR : ℂ) (x : ℝ) : ℂ :=
  (s.state (s.initial iL iR) x).value
def waveD (s : EvolutionSegment) (iL iR : ℂ) (x : ℝ) : ℂ :=
  (s.state (s.initial iL iR) x).slope

lemma exit_data (s : EvolutionSegment) (iL iR : ℂ) :
    s.transfer.act (s.initial iL iR)=s.right.encode ⟨(s.channels.outgoing iL iR).2,iR⟩ := by
  have h := channelTransfer_action s.left s.right s.transfer
    ⟨iL,(s.channels.outgoing iL iR).1⟩
  change s.right.encode (s.channels.act ⟨iL,(s.channels.outgoing iL iR).1⟩)=
    s.transfer.act (s.initial iL iR) at h
  rw [s.channels.outgoing_solves] at h
  exact h.symm

def Admissible (s : EvolutionSegment) (iL iR : ℂ) (f v : ℝ→ℂ) : Prop :=
  ClassicalState s.coefficient s.jumps f v ∧
  (s.left.decode ⟨f 0,v 0⟩).forward=iL ∧
  (s.right.decode ⟨f s.width,v s.width⟩).backward=iR

lemma wave_admissible (s : EvolutionSegment) (iL iR : ℂ) :
    s.Admissible iL iR (s.wave iL iR) (s.waveD iL iR) := by
  refine ⟨s.classical (s.initial iL iR),?_,?_⟩
  · change (s.left.decode (s.state (s.initial iL iR) 0)).forward=iL
    simp [initial]
  · change (s.right.decode (s.state (s.initial iL iR) s.width)).backward=iR
    rw [state_exit,exit_data,s.right.decode_encode]

lemma arbitrary_interior (s : EvolutionSegment) (f v : ℝ→ℂ)
    (h : ClassicalState s.coefficient s.jumps f v) (x : ℝ) (hx : x∈Icc 0 s.width) :
    (⟨f x,v x⟩:State)=s.evolution.flow ⟨f 0,v 0⟩ x := by
  apply s.evolution.state_representation s.width_pos f v
    (show Differentiable ℝ f from fun t=>(h.derivative t).differentiableAt).continuous
    h.continuous_slope (fun t _=>h.derivative t) _ x hx
  intro t ht
  have hj : t∉s.jumps := by
    rintro (hz|hL)
    · linarith [ht.1]
    · linarith [ht.2]
  simpa [coefficient,not_lt.mpr (le_of_lt ht.1),ht.2] using h.equation t hj

lemma arbitrary_endpoint (s : EvolutionSegment) (f v : ℝ→ℂ)
    (h : ClassicalState s.coefficient s.jumps f v) :
    (⟨f s.width,v s.width⟩:State)=s.transfer.act ⟨f 0,v 0⟩ :=
  s.arbitrary_interior f v h s.width ⟨le_of_lt s.width_pos,le_rfl⟩

lemma arbitrary_state (s : EvolutionSegment) (f v : ℝ→ℂ)
    (h : ClassicalState s.coefficient s.jumps f v) (x : ℝ) :
    (⟨f x,v x⟩:State)=s.state ⟨f 0,v 0⟩ x := by
  have hf : Continuous f :=
    (show Differentiable ℝ f from fun t=>(h.derivative t).differentiableAt).continuous
  by_cases hn : x<0
  · rw [state,if_pos hn]
    obtain ⟨h1,h2⟩ := s.left.profile.representation_on_closed_interval
      (l:=x-1) (r:=0) (o:=0) (by linarith) ⟨by linarith,le_rfl⟩
      f v hf h.continuous_slope (fun t _=>h.derivative t)
      (by
        intro t ht
        have hj : t∉s.jumps := by rintro (he|he) <;> linarith [ht.2,s.width_pos]
        simpa [coefficient,ht.2,Port.profile,LocalProfile.oscillatory,
          Complex.real_smul] using h.equation t hj)
      x ⟨by linarith,le_of_lt hn⟩
    apply State.ext
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,mul_comm] using h1
    · simpa [LocalProfile.flow,LocalProfile.transfer,RealTransfer.act,mul_comm,
        mul_left_comm,mul_assoc] using h2
  · rw [state,if_neg hn]
    by_cases hi : x<s.width
    · rw [tail,if_pos hi]
      exact s.arbitrary_interior f v h x ⟨le_of_not_gt hn,le_of_lt hi⟩
    · rw [tail,if_neg hi]
      have he := s.right.profile.state_representation
        (l:=s.width) (r:=x+1) (by linarith)
        f v hf h.continuous_slope (fun t _=>h.derivative t)
        (by
          intro t ht
          have ht0 : 0<t := lt_trans s.width_pos ht.1
          have hj : t∉s.jumps := by rintro (hz|hL) <;> linarith [ht.1]
          simpa [coefficient,not_lt.mpr (le_of_lt ht0),not_lt.mpr (le_of_lt ht.1),
            Port.profile,LocalProfile.oscillatory] using h.equation t hj)
        x ⟨le_of_not_gt hi,by linarith⟩
      rw [s.arbitrary_endpoint f v h] at he
      exact he

lemma arbitrary_unique (s : EvolutionSegment) (iL iR : ℂ) (f v : ℝ→ℂ)
    (h : s.Admissible iL iR f v) : f=s.wave iL iR ∧ v=s.waveD iL iR := by
  let l := s.left.decode ⟨f 0,v 0⟩
  let r := s.right.decode ⟨f s.width,v s.width⟩
  have he : s.channels.act l=r := by
    apply s.right.encode_injective
    rw [channels, channelTransfer_action]
    simp only [l, r, s.left.encode_decode, s.right.encode_decode]
    exact (s.arbitrary_endpoint f v h.1).symm
  have hl : l.forward=iL := h.2.1
  have hr : r.backward=iR := h.2.2
  have hlall : l=⟨iL,l.backward⟩ := by ext <;> simp [hl]
  have hrall : r=⟨r.forward,iR⟩ := by ext <;> simp [hr]
  rw [hlall,hrall] at he
  have hout := s.channels.outgoing_unique iL iR l.backward r.forward he
  have hbl : l.backward=(s.channels.outgoing iL iR).1 := congrArg Prod.fst hout
  have hi : (⟨f 0,v 0⟩:State)=s.initial iL iR := by
    have hh : l=⟨iL,(s.channels.outgoing iL iR).1⟩ := by ext <;> simp [hl,hbl]
    simpa [l,initial] using congrArg s.left.encode hh
  constructor <;> funext x
  · have hh := s.arbitrary_state f v h.1 x
    rw [hi] at hh
    exact congrArg State.value hh
  · have hh := s.arbitrary_state f v h.1 x
    rw [hi] at hh
    exact congrArg State.slope hh

theorem existsUnique_scattering (s : EvolutionSegment) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), s.Admissible iL iR fv.1 fv.2 := by
  refine ⟨(s.wave iL iR,s.waveD iL iR),s.wave_admissible iL iR,?_⟩
  intro fv hf
  obtain ⟨h1,h2⟩ := s.arbitrary_unique iL iR fv.1 fv.2 hf
  exact Prod.ext h1 h2

lemma current_formula (s : EvolutionSegment) (iL iR : ℂ) (hbar mass x : ℝ) :
    current hbar mass (s.wave iL iR) x=
      (hbar/mass)*(absSq iL-absSq (s.channels.outgoing iL iR).1) := by
  unfold current wave
  rw [(s.state_value_deriv (s.initial iL iR) x).deriv]
  have hh := s.state_flux (s.initial iL iR) x
  rw [initial,s.left.encode_flux] at hh
  exact congrArg (fun u=>(hbar/mass)*u) hh

/-- Shape-independent completion for any actual verified backend e. -/
theorem complete_scattering (s : EvolutionSegment) :
    (∀ iL iR, ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), s.Admissible iL iR fv.1 fv.2) ∧
    (∀ iL iR, ContDiff ℝ 1 (s.wave iL iR)) ∧
    (∀ iL iR x, x∉s.jumps → deriv (deriv (s.wave iL iR)) x=
      -(s.coefficient x:ℂ)*s.wave iL iR x) ∧
    (∀ iL iR h m x, current h m (s.wave iL iR) x=
      (h/m)*(absSq iL-absSq (s.channels.outgoing iL iR).1)) ∧
    s.channels.scatteringMatrix.conjTranspose*s.channels.scatteringMatrix=1 ∧
    s.channels.scatteringMatrix*s.channels.scatteringMatrix.conjTranspose=1 ∧
    s.channels.scatteringMatrix.transpose=s.channels.scatteringMatrix := by
  exact ⟨s.existsUnique_scattering,
    fun iL iR=>(s.classical (s.initial iL iR)).C1,
    fun iL iR x hx=>(s.classical (s.initial iL iR)).second_order x hx,
    s.current_formula,s.channels.unitary_matrix.1,s.channels.unitary_matrix.2,
    s.channels.symmetric_matrix⟩

end EvolutionSegment
end QuantumScattering
