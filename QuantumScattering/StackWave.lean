/- F1 candidate. Actual globally C1 waves on arbitrarily many layers.
Composition is inductive in List Layer, not a hard-coded number of regions.
Only first derivatives are glued across potential jumps. -/
import QuantumScattering.Splicing

noncomputable section
open Set Filter
open scoped Topology
namespace QuantumScattering

def Port.profile (p : Port) : LocalProfile := LocalProfile.oscillatory p.k p.positive

namespace Stack

/-- Interior and right lead, extrapolated to all x for convenient pasting.
In each recursive call the origin is the left edge of the remaining stack. -/
def tail (right : Port) : Stack → State → ℝ → State
  | [],y,x => right.profile.flow y x
  | s::rest,y,x => if x < s.width then s.flow y x
      else tail right rest (s.transfer.act y) (x-s.width)

def tailCoefficient (right : Port) : Stack → ℝ → ℝ
  | [],_ => right.k^2
  | s::rest,x => if x < s.width then s.delta
      else tailCoefficient right rest (x-s.width)

def tailJumps : Stack → List ℝ
  | [] => []
  | s::rest => s.width :: (tailJumps rest).map (fun x => s.width+x)

/-- Interface at the left edge is also listed, even if the adjacent potentials
happen to agree. Excluding a redundant jump only weakens an ODE domain, not C1. -/
def jumps (xs : Stack) : Set ℝ := {x | x=0 ∨ x∈tailJumps xs}

@[simp] lemma tail_zero (right : Port) (xs : Stack) (y : State) : tail right xs y 0=y := by
  cases xs with
  | nil => simp [tail]
  | cons s rest => simp [tail,s.width_pos]

lemma tail_derivative (right : Port) (xs : Stack) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (tail right xs y t).value) (tail right xs y x).slope x := by
  induction xs generalizing y x with
  | nil => exact right.profile.hasDerivAt_value y x
  | cons s rest ih =>
    have h := hasDerivAt_join s.width
      (fun t => (s.flow y t).value) (fun t => (s.flow y t).slope)
      (fun t => (tail right rest (s.transfer.act y) (t-s.width)).value)
      (fun t => (tail right rest (s.transfer.act y) (t-s.width)).slope)
      (s.hasDerivAt_value y)
      (fun t => by
        simpa [Function.comp_def] using
          (ih (s.transfer.act y) (t-s.width)).scomp t ((hasDerivAt_id t).sub_const s.width))
      (by simp [Layer.endpoint]) (by simp [Layer.endpoint]) x
    have heq : (fun t => (tail right (s::rest) y t).value) =
        join s.width (fun t => (s.flow y t).value)
          (fun t => (tail right rest (s.transfer.act y) (t-s.width)).value) := by
      funext t
      by_cases ht : t < s.width <;> simp [tail, join, ht]
    rw [heq]
    by_cases hx : x < s.width <;> simpa [tail, join, hx] using h

lemma tail_slope_continuous (right : Port) (xs : Stack) (y : State) :
    Continuous (fun t => (tail right xs y t).slope) := by
  induction xs generalizing y with
  | nil => exact right.profile.continuous_slope y
  | cons s rest ih =>
    have heq : (fun t => (tail right (s::rest) y t).slope) =
        join s.width (fun t => (s.flow y t).slope)
          (fun t => (tail right rest (s.transfer.act y) (t-s.width)).slope) := by
      funext t
      by_cases ht : t < s.width <;> simp [tail, join, ht]
    rw [heq]
    apply continuous_join
    · exact s.profile.continuous_slope y
    · exact (ih (s.transfer.act y)).comp (continuous_id.sub continuous_const)
    · simp [Layer.endpoint]

lemma tail_slope_derivative (right : Port) (xs : Stack) (y : State)
    (x : ℝ) (hx : x∉tailJumps xs) :
    HasDerivAt (fun t => (tail right xs y t).slope)
      (-(tailCoefficient right xs x : ℂ)*(tail right xs y x).value) x := by
  induction xs generalizing y x with
  | nil => exact right.profile.hasDerivAt_slope y x
  | cons s rest ih =>
    have hne : x≠s.width := by
      intro h; apply hx; simp [tailJumps,h]
    by_cases hlt : x<s.width
    · simp only [tailCoefficient,tail,if_pos hlt]
      apply (s.hasDerivAt_slope y x).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hlt] with t ht
      simp only [tail,if_pos (show t<s.width from ht)]
    · have hgt : s.width<x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      have hrest : x-s.width∉tailJumps rest := by
        intro hm
        apply hx
        simp only [tailJumps,List.mem_cons,List.mem_map]
        right
        exact ⟨x-s.width,hm,by ring⟩
      have hd := (ih (s.transfer.act y) (x-s.width) hrest).scomp x
        ((hasDerivAt_id x).sub_const s.width)
      simp only [tailCoefficient,tail,if_neg hlt]
      apply (show HasDerivAt
        (fun t => (tail right rest (s.transfer.act y) (t-s.width)).slope)
        (-(tailCoefficient right rest (x-s.width) : ℂ)*
          (tail right rest (s.transfer.act y) (x-s.width)).value) x from by simpa [Function.comp_def] using hd).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hgt] with t ht
      simp only [tail,if_neg (not_lt.mpr (le_of_lt (show s.width<t from ht)))]

lemma tail_flux (right : Port) (xs : Stack) (y : State) (x : ℝ) :
    (tail right xs y x).flux=y.flux := by
  induction xs generalizing y x with
  | nil => exact right.profile.flux_preserved y x
  | cons s rest ih =>
    by_cases h : x<s.width
    · simpa only [tail,if_pos h] using s.flux_preserved y x
    · simp only [tail,if_neg h]
      rw [ih,s.transfer.flux_preserved]

/-- Beyond the last interface, the wave is the right free evolution of the
actual composed exit data. This is the bridge from PDE segments to transfer. -/
lemma tail_right (right : Port) (xs : Stack) (y : State) (x : ℝ)
    (hx : width xs ≤ x) :
    tail right xs y x=right.profile.flow ((transfer xs).act y) (x-width xs) := by
  induction xs generalizing y x with
  | nil => simp [tail,transfer,width]
  | cons s rest ih =>
    have hrest : width rest ≤ x-s.width := by simp only [width] at hx; linarith
    have hlt : ¬x<s.width := by have hn := width_nonneg rest; simp [width] at hx; linarith
    rw [tail,if_neg hlt,ih _ _ hrest]
    simp only [transfer,RealTransfer.after_act,width]
    congr 1
    ring

/-- The global state, including the true left lead. -/
def waveState (left right : Port) (xs : Stack) (y : State) (x : ℝ) : State :=
  if x<0 then left.profile.flow y x else tail right xs y x

def coefficient (left right : Port) (xs : Stack) (x : ℝ) : ℝ :=
  if x<0 then left.k^2 else tailCoefficient right xs x

@[simp] lemma waveState_zero (left right : Port) (xs : Stack) (y : State) :
    waveState left right xs y 0=y := by simp [waveState]

lemma wave_derivative (left right : Port) (xs : Stack) (y : State) (x : ℝ) :
    HasDerivAt (fun t => (waveState left right xs y t).value)
      (waveState left right xs y x).slope x := by
  have h := hasDerivAt_join 0
    (fun t => (left.profile.flow y t).value) (fun t => (left.profile.flow y t).slope)
    (fun t => (tail right xs y t).value) (fun t => (tail right xs y t).slope)
    (left.profile.hasDerivAt_value y) (tail_derivative right xs y) (by simp) (by simp) x
  have heq : (fun t => (waveState left right xs y t).value) =
      join 0 (fun t => (left.profile.flow y t).value) (fun t => (tail right xs y t).value) := by
    funext t
    by_cases ht : t < 0 <;> simp [waveState, join, ht]
  rw [heq]
  by_cases hx : x < 0 <;> simpa [waveState, join, hx] using h

lemma wave_slope_continuous (left right : Port) (xs : Stack) (y : State) :
    Continuous (fun t => (waveState left right xs y t).slope) := by
  have heq : (fun t => (waveState left right xs y t).slope) =
      join 0 (fun t => (left.profile.flow y t).slope) (fun t => (tail right xs y t).slope) := by
    funext t
    by_cases ht : t < 0 <;> simp [waveState, join, ht]
  rw [heq]
  exact continuous_join 0 _ _ (left.profile.continuous_slope y)
    (tail_slope_continuous right xs y) (by simp)

lemma wave_slope_derivative (left right : Port) (xs : Stack) (y : State)
    (x : ℝ) (hx : x∉jumps xs) :
    HasDerivAt (fun t => (waveState left right xs y t).slope)
      (-(coefficient left right xs x : ℂ)*(waveState left right xs y x).value) x := by
  have h0 : x≠0 := fun h => hx (Or.inl h)
  have hj : x∉tailJumps xs := fun h => hx (Or.inr h)
  by_cases hn : x<0
  · simp only [coefficient,waveState,if_pos hn]
    apply (left.profile.hasDerivAt_slope y x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hn] with t ht
    simp only [waveState,if_pos (show t<0 from ht)]
  · have hp : 0<x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm h0)
    simp only [coefficient,waveState,if_neg hn]
    apply (tail_slope_derivative right xs y x hj).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hp] with t ht
    simp only [waveState,if_neg (not_lt.mpr (le_of_lt (show 0<t from ht)))]

theorem classical_wave (left right : Port) (xs : Stack) (y : State) :
    ClassicalState (coefficient left right xs) (jumps xs)
      (fun x => (waveState left right xs y x).value)
      (fun x => (waveState left right xs y x).slope) :=
  ⟨wave_derivative left right xs y,wave_slope_continuous left right xs y,
    wave_slope_derivative left right xs y⟩

theorem wave_flux (left right : Port) (xs : Stack) (y : State) (x : ℝ) :
    (waveState left right xs y x).flux=y.flux := by
  by_cases h : x<0
  · simpa only [waveState,if_pos h] using left.profile.flux_preserved y x
  · simpa only [waveState,if_neg h] using tail_flux right xs y x

theorem actual_current (left right : Port) (xs : Stack) (y : State)
    (hbar mass x : ℝ) :
    current hbar mass (fun t => (waveState left right xs y t).value) x=
      (hbar/mass)*y.flux := by
  unfold current
  rw [(wave_derivative left right xs y x).deriv]
  exact congrArg (fun u => (hbar/mass)*u) (wave_flux left right xs y x)

lemma waveState_exit (left right : Port) (xs : Stack) (y : State) :
    waveState left right xs y (width xs)=(transfer xs).act y := by
  rw [waveState,if_neg (not_lt.mpr (width_nonneg xs)),tail_right right xs y _ le_rfl]
  simp

end Stack
end QuantumScattering
