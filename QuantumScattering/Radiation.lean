/- F2: only asymptotic incoming channels are prescribed; the outgoing channels
and the exterior modal representation are conclusions of the actual ODE.
The channels are flux-normalized and use each boundary as phase origin.
Uncompiled proof candidates. -/
import QuantumScattering.Framework
import QuantumScattering.FlowComposition

noncomputable section
open Filter Set
open scoped Topology
namespace QuantumScattering
namespace Port

/-- Undo free propagation back to the chosen phase origin, then decode the
state. This is the dephased, flux-normalized traveling coefficient pair. -/
def extractAt (p : Port) (o x : ℝ) (y : State) : Modes :=
  p.decode ((p.profile.transfer (x-o)).reverse.act y)

/-- Both coordinates depend on f and its ACTUAL derivative. -/
def modesAt (p : Port) (o : ℝ) (f : ℝ→ℂ) (x : ℝ) : Modes :=
  p.extractAt o x ⟨f x,deriv f x⟩

lemma extract_free (p : Port) (o x : ℝ) (y : State) :
    p.extractAt o x (p.profile.flow y (x-o))=p.decode y := by
  simp only [extractAt,LocalProfile.flow,← RealTransfer.after_act,
    RealTransfer.reverse_after,RealTransfer.identity_act]

/-- Reconstruct the actual state from extracted modes, without an ansatz. -/
lemma extract_reconstruct (p : Port) (o x : ℝ) (y : State) :
    p.profile.flow (p.encode (p.extractAt o x y)) (x-o)=y := by
  simp only [extractAt,p.encode_decode,LocalProfile.flow,← RealTransfer.after_act,
    RealTransfer.after_reverse,RealTransfer.identity_act]

lemma extract_plane_value (p : Port) (o x : ℝ) (y : State) :
    y.value=((p.extractAt o x y).forward*plane p.k (x-o)+
      (p.extractAt o x y).backward*plane (-p.k) (x-o))/(p.root:ℂ) := by
  have h := congrArg State.value (p.extract_reconstruct o x y)
  rw [p.free_mode_value] at h
  exact h.symm
end Port

namespace Problem
lemma arbitrary_left_modes (p : Problem) (f v : ℝ→ℂ)
    (h : ClassicalState p.coefficient p.jumps f v) (x : ℝ) (hx : x<0) :
    p.left.modesAt 0 f x=p.left.decode ⟨f 0,v 0⟩ := by
  have hs := p.arbitrary_state_representation h x
  rw [Stack.waveState,if_pos hx] at hs
  unfold Port.modesAt
  rw [h.deriv_eq,hs]
  simpa only [sub_zero] using p.left.extract_free 0 x ⟨f 0,v 0⟩

lemma arbitrary_right_modes (p : Problem) (f v : ℝ→ℂ)
    (h : ClassicalState p.coefficient p.jumps f v) (x : ℝ)
    (hx : Stack.width p.layers≤x) :
    p.right.modesAt (Stack.width p.layers) f x=
      p.right.decode ⟨f (Stack.width p.layers),v (Stack.width p.layers)⟩ := by
  have h0 : 0≤x := le_trans (Stack.width_nonneg _) hx
  have hs := p.arbitrary_state_representation h x
  rw [Stack.waveState,if_neg (not_lt.mpr h0),Stack.tail_right _ _ _ _ hx] at hs
  change (⟨f x,v x⟩:State)=p.right.profile.flow
    (p.transfer.act ⟨f 0,v 0⟩) (x-Stack.width p.layers) at hs
  rw [← p.arbitrary_endpoint h] at hs
  unfold Port.modesAt
  rw [h.deriv_eq,hs]
  exact p.right.extract_free (Stack.width p.layers) x _

/-- No outgoing data, elementary span, interior basis, or current balance is
an input assumption. All discontinuities remain explicit in p.jumps. -/
def IncomingAtInfinity (p : Problem) (iL iR : ℂ) (f : ℝ→ℂ) : Prop :=
  ClassicalState p.coefficient p.jumps f (deriv f) ∧
  Tendsto (fun x => (p.left.modesAt 0 f x).forward) atBot (𝓝 iL) ∧
  Tendsto (fun x => (p.right.modesAt (Stack.width p.layers) f x).backward)
    atTop (𝓝 iR)

lemma incoming_iff_admissible (p : Problem) (iL iR : ℂ) (f : ℝ→ℂ) :
    p.IncomingAtInfinity iL iR f ↔ p.Admissible iL iR f (deriv f) := by
  constructor
  · rintro ⟨hs,hl,hr⟩
    have hleft : Tendsto (fun x=>(p.left.modesAt 0 f x).forward) atBot
        (𝓝 (p.left.decode ⟨f 0,deriv f 0⟩).forward) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
      exact (congrArg Modes.forward (p.arbitrary_left_modes f (deriv f) hs x hx)).symm
    have hright : Tendsto
        (fun x=>(p.right.modesAt (Stack.width p.layers) f x).backward) atTop
        (𝓝 (p.right.decode ⟨f (Stack.width p.layers),deriv f (Stack.width p.layers)⟩).backward) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Stack.width p.layers)] with x hx
      exact (congrArg Modes.backward (p.arbitrary_right_modes f (deriv f) hs x hx)).symm
    exact ⟨hs,tendsto_nhds_unique hleft hl,tendsto_nhds_unique hright hr⟩
  · rintro ⟨hs,hl,hr⟩
    refine ⟨hs,?_,?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
      rw [p.arbitrary_left_modes f (deriv f) hs x hx,hl]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Stack.width p.layers)] with x hx
      rw [p.arbitrary_right_modes f (deriv f) hs x hx,hr]

lemma wave_incoming (p : Problem) (iL iR : ℂ) :
    p.IncomingAtInfinity iL iR (p.wave iL iR) := by
  apply (p.incoming_iff_admissible iL iR _).mpr
  rw [(p.classical iL iR).deriv_eq]
  exact p.wave_admissible iL iR

/-- A unique actual wave for prescribed incoming limits at both infinities. -/
theorem existsUnique_incoming_at_infinity (p : Problem) (iL iR : ℂ) :
    ∃! f : ℝ→ℂ, p.IncomingAtInfinity iL iR f := by
  refine ⟨p.wave iL iR,p.wave_incoming iL iR,?_⟩
  intro f hf
  exact (p.arbitrary_scattering_unique iL iR f (deriv f)
    ((p.incoming_iff_admissible iL iR f).mp hf)).1

/-- General finite-layer current conservation applies to arbitrary classical
solutions, not just to a preselected constructed wave. -/
theorem current_arbitrary_classical (p : Problem) (f v : ℝ→ℂ)
    (h : ClassicalState p.coefficient p.jumps f v) (hbar mass x : ℝ) :
    current hbar mass f x=(hbar/mass)*(⟨f 0,v 0⟩:State).flux := by
  unfold current
  rw [h.deriv_eq]
  have hs := p.arbitrary_state_representation h x
  have hflux := congrArg State.flux hs
  rw [Stack.wave_flux] at hflux
  exact congrArg (fun u => (hbar/mass)*u) hflux
end Problem
end QuantumScattering
